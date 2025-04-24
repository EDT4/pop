import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Pop.CategoryTheory.OplaxPullback
import Pop.CategoryTheory.OplaxPullback.Comma

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type _} [Category A] [pua : HasPushouts A]
variable {B : Type _} [Category B] [pub : HasPushouts B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C) [pnl : PreservesColimitsOfShape ℕ L]
variable (R : B ⥤ C) [pnr : PreservesColimitsOfShape ℕ R]
variable (Lb : C ⥤ A)
variable (Rb : C ⥤ B)
variable (Ladj : Lb ⊣ L)
variable (Radj : Rb ⊣ R)

namespace CategoryTheory.OplaxPullback

@[simps!]
noncomputable def to_comma' : OplaxPullback L R ⥤ Comma L R where
  obj o := {
    left   := o.left
    right  := pushout (X := Rb.obj o.middle) (Y := Rb.obj (L.obj o.left)) (Z := o.right) (Rb.map o.homl) ((Radj.homEquiv _ _).invFun o.homr)
    hom    := Radj.unit.app (L.obj o.left) ≫ R.map (pushout.inl _ _)
  }
  map f := {
    left := f.left
    right := pushout.map _ _ _ _ (Rb.map (L.map f.left)) (f.right) (Rb.map f.middle)
      (by rw [← Functor.map_comp,← Functor.map_comp,OplaxPullback.Hom.wl])
      (by rw [Equiv.invFun_as_coe,Adjunction.homEquiv_counit,Equiv.invFun_as_coe,Adjunction.homEquiv_counit,← Category.assoc,← Functor.map_comp,← OplaxPullback.Hom.wr,Functor.map_comp,Category.assoc,Category.assoc,Adjunction.counit_naturality])
    w := by
      dsimp only [Adjunction.homEquiv]
      simp [← Functor.map_comp]
      simp only [Functor.map_comp, Adjunction.unit_naturality_assoc]
  }
  map_comp f g := by
    dsimp [Adjunction.homEquiv]
    ext <;> simp

@[simps!]
noncomputable def to_comma : OplaxPullback L R ⥤ Comma L R :=
  let pl := (whiskerRight (OplaxPullback.llm _ _) Rb)
  let pr := ((Adjunction.homEquiv (Adjunction.whiskerRight _ Radj) _ _).invFun (OplaxPullback.rrm _ _))
  Comma.lift
    (OplaxPullback.projLeft _ _)
    (pushout
      (X := OplaxPullback.projMid _ _ ⋙ Rb)
      (Y := OplaxPullback.projLeft _ _ ⋙ L ⋙ Rb)
      (Z := OplaxPullback.projRight _ _)
      pl pr
    )
    (
      (Functor.rightUnitor _ ).inv
      ≫ whiskerLeft (OplaxPullback.projLeft L R ⋙ L) Radj.unit
      ≫ (whiskerRight (pushout.inl pl pr) R)
    )

-- @[reassoc (attr := simp)] -- TODO: Cannot reassoc functor comp?
def to_comma_fst : to_comma L R Rb Radj ⋙ Comma.fst L R = OplaxPullback.projLeft L R
  := Comma.lift_fst

-- TODO: Separate the stuff in to_comma, then prove to_from_comma_adj using that. See how to_comma_fst is used for example
def to_comma_snd : to_comma L R Rb Radj ⋙ Comma.snd L R = OplaxPullback.projRight L R
  := sorry -- Comma.lift_snd

noncomputable def to_from_comma_adj : OplaxPullback.to_comma L R Rb Radj ⊣ OplaxPullback.from_comma L R where
  unit := sorry
  counit := Comma.liftTrans
    (by rw [Functor.assoc,OplaxPullback.to_comma_fst,OplaxPullback.from_comma_projLeft] ; exact (Functor.leftUnitor _).inv)
    (by rw [Functor.assoc,OplaxPullback.to_comma_snd] ; sorry)
    sorry
  -- unit := {
  --   app o := {
  --     left := 𝟙 _
  --     middle := o.homl
  --     right := pushout.inr _ _
  --     wl := by
  --       simp only [Functor.id_obj,CategoryTheory.Functor.map_id,Category.comp_id,Functor.comp_obj,OplaxPullback.from_comma_obj_homl,to_comma_obj_left]
  --       exact (Category.comp_id _).symm
  --     wr := by
  --       simp [Adjunction.homEquiv]
  --       let cond := congr_arg (Radj.unit.app o.middle ≫ ·) (congr_arg G.map (pushout.condition (f := Rb.map o.homl) (g := (Radj.homEquiv _ _).invFun o.homr)))
  --       simp [Adjunction.homEquiv] at cond
  --       exact cond.symm
  --   }
  -- }
  -- counit := {
  --   app o := {
  --     left := 𝟙 _
  --     right := pushout.desc
  --       (Rb.map o.hom ≫ Radj.counit.app o.right)
  --       (𝟙 _)
  --       (by simp [Adjunction.homEquiv])
  --     w := by
  --       let eq : Rb.map (𝟙 (F.obj o.left)) ≫ Rb.map o.hom ≫ Radj.counit.app o.right = (Rb.map o.hom ≫ Radj.counit.app o.right) ≫ 𝟙 o.right := by simp
  --       simp [Adjunction.homEquiv] -- TODO: -Functor.map_comp ?
  --       rw [← Functor.map_comp]
  --       simp [pushout.inl_desc _ _ eq]
  --   }
  --   naturality x y f := by
  --     ext
  --     . simp [to_comma,OplaxPullback.from_comma]
  --     . simp [to_comma,OplaxPullback.from_comma,(·≫·),Adjunction.homEquiv,f.w,pushout.map]
  --       sorry -- TODO: pushout.desc and composition?
  -- }
  -- := Adjunction.CoreEtaInvertibleHom.mk
  --   {app o := {
  --     left := 𝟙 _
  --     middle := o.homl
  --     right := pushout.inr _ _
  --     wl := by
  --       simp only [Functor.id_obj,CategoryTheory.Functor.map_id,Category.comp_id,Functor.comp_obj,OplaxPullback.from_comma_obj_homl,to_comma_obj_left]
  --       exact (Category.comp_id _).symm
  --     wr := by
  --       simp [Adjunction.homEquiv]
  --       let cond := congr_arg (Radj.unit.app o.middle ≫ ·) (congr_arg G.map (pushout.condition (f := Rb.map o.homl) (g := (Radj.homEquiv _ _).invFun o.homr)))
  --       simp [Adjunction.homEquiv] at cond
  --       exact cond.symm
  --     }}
  --   (fun {x y} f => by
  --     simp [to_comma,OplaxPullback.from_comma,(·≫·),OplaxPullback.liftL,OplaxPullback.lift,Comma.fst,Comma.snd,Comma.natTrans] at f
  --     exact {
  --       left := f.left
  --       right := pushout.desc
  --         (Rb.map (F.map f.left ≫ y.hom) ≫ Radj.counit.app _)
  --         f.right
  --         (by
  --           simp [to_comma,OplaxPullback.from_comma,(·≫·),Adjunction.homEquiv]
  --           simp [← Functor.map_comp,← Category.assoc]
  --           let test := f.wl
  --           let test2 := f.wr
  --           dsimp at test
  --           dsimp at test2
  --           sorry
  --         )
  --       w := sorry
  --     }
  --   )
  --   sorry
  --   sorry


-- noncomputable def OplaxPullback.to_flipped_comma : OplaxPullback L R ⥤ Comma G F
--   := OplaxPullback.flip ⋙ OplaxPullback.to_comma G F Lb Ladj
--
-- noncomputable def OplaxPullback.to_from_flipped_comma_adj : OplaxPullback.to_flipped_comma L R Lb Ladj ⊣ OplaxPullback.from_flipped_comma L R
--   := by
--     rw [← OplaxPullback.from_comma_flip]
--     exact Adjunction.comp OplaxPullback.flip_equiv.toAdjunction (OplaxPullback.to_from_comma_adj _ _ _ _)
