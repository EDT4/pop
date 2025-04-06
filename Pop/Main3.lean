import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Monotone.Defs
import Pop.CategoryTheory.Adjunction.MkExtras
import Pop.CategoryTheory.Limits.OplaxPullbackThing
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.CategoryTheory.OplaxPullbackThing
import Pop.NatCategoryExtras
import Pop.NatExtras
import Pop.Util

-- set_option pp.proofs true

section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

local instance temp : (Nat.Functor.mulr 2).Final := Nat.Functor.mulr_final -- TODO: Cannot find this instance?

variable {C : Type _}
variable [cat : Category C]
variable [hsc : HasSeqColimits C] -- TODO: Reason for noncomputable. Maybe change later? It seems like most stuff is built on using limit/colimit instead of the cones directly though.
variable (A : Set C)
variable (B : Set C)
variable [ra : Reflective (fullSubcategoryInclusion A)] -- TODO: Reflective includes full and faithful, but it is already implied by the full subcategory.
variable [rb : Reflective (fullSubcategoryInclusion B)]
variable (closed_a : ClosedUnderColimitsOfShape ℕ A)
variable (closed_b : ClosedUnderColimitsOfShape ℕ B)
variable [cia : IsClosedUnderIsomorphisms A]
variable [cib : IsClosedUnderIsomorphisms B]
omit [_]

abbrev fullSubcategoryAdj     := reflectorAdjunction (fullSubcategoryInclusion A)
abbrev fullSubcategoryMonad   := (reflectorAdjunction (fullSubcategoryInclusion A)).toMonad
abbrev fullSubcategoryComonad := (reflectorAdjunction (fullSubcategoryInclusion A)).toComonad

-- TODO: Rename stuff when the proof is finished
namespace IntersectionReflective
  def sequence : Limits.Seq (C ⥤ C) :=
    let TA := fullSubcategoryMonad A
    let TB := fullSubcategoryMonad B
    Seq.iterate2 (c := Cat.of C) (.mk TA.toFunctor TA.η) (.mk TB.toFunctor TB.η)

  section include C cat A B ra rb
  lemma sequence_odd {n} : ∀{c}, A (((sequence A B).obj (n * 2 + 1)).obj c) := by
    induction n
    . exact FullSubcategory.property _
    . rw [Nat.add_mul]
      intro
      apply_assumption
  lemma sequence_even {n} : ∀{c}, B (((sequence A B).obj (n * 2 + 2)).obj c) := sequence_odd B A
  end

  noncomputable abbrev Minf : C ⥤ C := colimit (sequence A B).diagram
  notation "M∞" => Minf

  variable {A B}

  section include C cat A B ra rb hsc cia closed_a
  lemma Minf_in_left (c : C) : A ((M∞ A B).obj c) := by
    apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
    apply IsClosedUnderIsomorphisms.of_iso (Nat.StrictMono.comp_seqColim_iso (·*2+1) (StrictMono.add_const (StrictMono.mul_const strictMono_id (by decide)) _))
    apply ClosedUnderColimitsOfShape.colimit closed_a
    intro
    apply sequence_odd
  end

  section include C cat A B ra rb hsc cib closed_b
  lemma Minf_in_right (c : C) : B ((M∞ A B).obj c) := by
    apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
    apply IsClosedUnderIsomorphisms.of_iso (Nat.StrictMono.comp_seqColim_iso (·*2+2) (StrictMono.add_const (StrictMono.mul_const strictMono_id (by decide)) _))
    apply ClosedUnderColimitsOfShape.colimit closed_b
    intro
    apply sequence_even
  end

  -- TODO: Naming? Will be used in other places.
  noncomputable abbrev L : C ⥤ FullSubcategory (A ∩ B : Set C) :=
    FullSubcategory.lift
      (A ∩ B : Set C)
      (M∞ A B)
      (fun c => .intro (Minf_in_left closed_a c) (Minf_in_right closed_b c))

  -- TODO: Inverse to (sequence A B).map n ?
  -- let test {n} : (sequence A B).obj n.succ ⟶ (sequence A B).obj n := by
  --   simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r]
  --   sorry

  noncomputable abbrev l' {c} (cmem : c ∈ A ∩ B) : (M∞ A B).obj c ⟶ c :=
    let base := (fullSubcategoryAdj A).counit.app ((FullSubcategory.map fun _ => And.left).obj (.mk c cmem))
    let F := (sequence A B).diagram.flip.obj c
    let F' := (sequence A B).diagram.flip.map base
    let convF : (M∞ A B).obj c ⟶ colimit F := ((colimitIsoFlipCompColim (sequence A B).diagram).app c).hom
    let h : (n : ℕ) → F.obj n ⟶ c := Nat.rec (𝟙 c) fun n r => sorry ≫ r -- (by simp [F,sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r] ; sorry)
    let Eh : colimit F ⟶ c := colimit.desc F (.mk c $ NatTrans.ofSequence h sorry)
    convF ≫ Eh

  noncomputable abbrev l'' : fullSubcategoryInclusion (A ∩ B : Set C) ⋙ M∞ A B ⟶ fullSubcategoryInclusion (A ∩ B : Set C) where
    app c :=
      let base := (fullSubcategoryAdj A).counit.app ((FullSubcategory.map fun _ => And.left).obj c)
      let F := (sequence A B).diagram.flip.obj c.obj
      let f := (sequence A B).diagram.flip.map base
      let conv : (M∞ A B).obj c.obj ⟶ colimit F := ((colimitIsoFlipCompColim (sequence A B).diagram).app c.obj).hom
      let s n : F.obj n.succ ⟶ F.obj n := by simp [F,sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r] ; sorry
      let h : (n : ℕ) → F.obj n ⟶ c.obj := Nat.rec (𝟙 c.obj) fun n r => s n ≫ r
      let Eh : colimit F ⟶ c.obj := colimit.desc F (.mk c.obj $ NatTrans.ofSequence h sorry)
      conv ≫ Eh

end IntersectionReflective

noncomputable def intersectionReflective : Reflective (fullSubcategoryInclusion (A ∩ B : Set C)) :=
  let L := IntersectionReflective.L closed_a closed_b
  {
    L := L
    adj := Adjunction.CoreEtaInvertibleHom.mk
      (seqColim.ι (IntersectionReflective.sequence A B) 0)
      (fun f => L.map f ≫ IntersectionReflective.l''.app _)
      (fun f => sorry)
      (fun f => sorry)
  }

namespace Lemma2
  variable {A : Type _} [Category A] [hsa : HasSeqColimits A] [pua : HasPushouts A]
  variable {B : Type _} [Category B] [hsb : HasSeqColimits B] [pub : HasPushouts B]
  variable (F : A ⥤ C) [pnf : PreservesColimitsOfShape ℕ F]
  variable (G : B ⥤ C) [png : PreservesColimitsOfShape ℕ G]
  variable (Fb : C ⥤ A)
  variable (Gb : C ⥤ B)
  variable (Fadj : Fb ⊣ F)
  variable (Gadj : Gb ⊣ G)

  def Pl  : Set (OplaxPullbackThing F G) := fun p => IsIso p.homl -- Partiallyₗ-oplax pullback.
  def Pr  : Set (OplaxPullbackThing F G) := fun p => IsIso p.homr -- Partiallyᵣ-oplax pullback.
  def Plr : Set (OplaxPullbackThing F G) := (Pl F G) ∩ (Pr F G)   -- Pullback.

  def comma_pl : Comma F G ⥤ FullSubcategory (Pl F G)
    := FullSubcategory.lift
      (Pl F G)
      (OplaxPullbackThing.byComma F G)
      (by simp [OplaxPullbackThing.byComma,Pl] ; infer_instance)

  def comma_pr : Comma G F ⥤ FullSubcategory (Pr F G)
    := FullSubcategory.lift
      (Pr F G)
      (OplaxPullbackThing.byFlippedComma F G)
      (by simp [OplaxPullbackThing.byFlippedComma,Pr] ; infer_instance)

  noncomputable def pl_comma : FullSubcategory (Pl F G) ⥤ Comma F G where
    obj p := {
      left := p.obj.left
      right := p.obj.right
      hom := inv _ (I := p.property) ≫ p.obj.homr
    }
    map f := {
      left := f.left
      right := f.right
    }

  noncomputable def pr_comma : FullSubcategory (Pr F G) ⥤ Comma G F where
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
  --   simp only [comma_pl,pl_comma,OplaxPullbackThing.byComma]
  --   exact {
  --     hom := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
  --     inv := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
  --   }

  -- noncomputable def comma_pr_inverse : comma_pr F G ⋙ pr_comma F G ≅ 𝟭 (Comma G F) := by
  --   simp only [comma_pr,pr_comma,OplaxPullbackThing.byFlippedComma]
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
  --       wr := by simp only [pl_comma,comma_pl,OplaxPullbackThing.byComma,OplaxPullbackThing.liftL,Comma.natTrans_app,FullSubcategory.lift,Functor.comp_obj,Functor.id_obj,CategoryTheory.Functor.map_id,Category.comp_id]
  --     }
  --     naturality x y f := by
  --       apply OplaxPullbackThing.Hom.ext
  --       . apply (Eq.trans OplaxPullbackThing.comp_left ·)
  --         apply (Eq.trans · OplaxPullbackThing.comp_left)
  --         simp only [OplaxPullbackThing.category,pl_comma,comma_pl,OplaxPullbackThing.byComma,OplaxPullbackThing.liftL,Comma.fst_map,FullSubcategory.lift,Functor.id_obj,Functor.comp_map,Category.comp_id,Functor.id_map,Category.id_comp]
  --       . apply (Eq.trans OplaxPullbackThing.comp_middle ·)
  --         apply (Eq.trans · OplaxPullbackThing.comp_middle)
  --         simp only [pl_comma,comma_pl,Functor.comp_obj,Functor.comp_map,FullSubcategory.lift_map,OplaxPullbackThing.byComma_map_middle,Functor.id_map,OplaxPullbackThing.comp_middle,IsIso.eq_inv_comp,OplaxPullbackThing.Hom.wl_assoc,IsIso.hom_inv_id,Category.comp_id]
  --       . apply (Eq.trans OplaxPullbackThing.comp_right ·)
  --         apply (Eq.trans · OplaxPullbackThing.comp_right)
  --         simp only [OplaxPullbackThing.category,pl_comma,comma_pl,OplaxPullbackThing.byComma,OplaxPullbackThing.liftL,Comma.snd_map, FullSubcategory.lift,Functor.id_obj,Functor.comp_map,Category.comp_id,Functor.id_map,Category.id_comp]
  --   }
  --   inv := {
  --     app x := {
  --       left := 𝟙 _
  --       middle := x.obj.homl
  --       right := 𝟙 _
  --       wl := by simp only [Functor.id_obj,pl_comma,comma_pl,OplaxPullbackThing.byComma,OplaxPullbackThing.liftL,Comma.natTrans_app,Functor.comp_obj,FullSubcategory.lift_obj_obj,CategoryTheory.Functor.map_id,Category.comp_id]
  --       wr := by
  --         simp [pl_comma,comma_pl,OplaxPullbackThing.byComma,OplaxPullbackThing.liftL]
  --         sorry
  --     }
  --     naturality := sorry
  --   }

  -- TODO: Maybe there is an easier way
  instance Pl.closed_iso : IsClosedUnderIsomorphisms (Pl F G) := sorry
    -- where
    -- of_iso i p := by
    --   obtain ⟨f,⟨i1,i2⟩⟩ := p.out
    --   simp [Pl]
    --   simp [Pl] at p
    --   let wll := i.inv.wl
    --   iterate 3 constructor
    --   . sorry
    --   . sorry
    --   . exact F.map (OplaxPullbackThing.leftIso i).inv ≫ f ≫ (OplaxPullbackThing.middleIso i).hom
    --   -- exact {out := ⟨ , ⟨sorry , sorry⟩⟩}
  instance Pr.closed_iso : IsClosedUnderIsomorphisms (Pr F G) := sorry

  local instance [hc : HasSeqColimits C] : HasSeqColimits (OplaxPullbackThing F G)
    := OplaxPullbackThing.hasColimitsOfShape

  section
    variable {F G}
    def OplaxPullbackThing.FullSubcategory.leftFunctor (S : Set (OplaxPullbackThing F G)) : FullSubcategory S ⥤ A
      := fullSubcategoryInclusion S ⋙ OplaxPullbackThing.leftFunctor F G

    def OplaxPullbackThing.FullSubcategory.middleFunctor (S : Set (OplaxPullbackThing F G)) : FullSubcategory S ⥤ C
      := fullSubcategoryInclusion S ⋙ OplaxPullbackThing.middleFunctor F G

    def OplaxPullbackThing.FullSubcategory.rightFunctor (S : Set (OplaxPullbackThing F G)) : FullSubcategory S ⥤ B
      := fullSubcategoryInclusion S ⋙ OplaxPullbackThing.rightFunctor F G
  end

  abbrev Pl.left   : FullSubcategory (Pl  F G) ⥤ A := OplaxPullbackThing.FullSubcategory.leftFunctor  (Pl  F G)
  abbrev Pr.left   : FullSubcategory (Pl  F G) ⥤ A := OplaxPullbackThing.FullSubcategory.leftFunctor  (Pl  F G)
  abbrev Plr.left  : FullSubcategory (Plr F G) ⥤ A := OplaxPullbackThing.FullSubcategory.leftFunctor  (Plr F G)
  abbrev Pl.right  : FullSubcategory (Pl  F G) ⥤ B := OplaxPullbackThing.FullSubcategory.rightFunctor (Pl  F G)
  abbrev Pr.right  : FullSubcategory (Pl  F G) ⥤ B := OplaxPullbackThing.FullSubcategory.rightFunctor (Pl  F G)
  abbrev Plr.right : FullSubcategory (Plr F G) ⥤ B := OplaxPullbackThing.FullSubcategory.rightFunctor (Plr F G)

  def OplaxPullbackThing.unleft : A ⥤ OplaxPullbackThing F G
    := OplaxPullbackThing.liftL F G
      (𝟭 A)
      (F ⋙ Gb)
      ((Functor.leftUnitor F).hom ≫ (Functor.rightUnitor F).inv ≫ whiskerLeft F Gadj.unit ≫ (Functor.associator F Gb G).inv)

  def OplaxPullbackThing.unright : B ⥤ OplaxPullbackThing F G
    := OplaxPullbackThing.liftR F G
      (G ⋙ Fb)
      (𝟭 B)
      ((Functor.leftUnitor G).hom ≫ (Functor.rightUnitor G).inv ≫ whiskerLeft G Fadj.unit ≫ (Functor.associator G Fb F).inv)

  def Pl.unleft : A ⥤ FullSubcategory (Pl F G)
    := FullSubcategory.lift
      (Pl F G)
      (OplaxPullbackThing.unleft F G Gb Gadj)
      (fun a => IsIso.id (F.obj a))

  def Pl.unright : B ⥤ FullSubcategory (Pl F G)
    := FullSubcategory.lift
      (Pl F G)
      (OplaxPullbackThing.unright F G Fb Fadj)
      (fun b => by simp [OplaxPullbackThing.unright,OplaxPullbackThing.liftR,Pl] ; sorry)

  def Pr.unright : B ⥤ FullSubcategory (Pr F G)
    := FullSubcategory.lift
      (Pr F G)
      (OplaxPullbackThing.unright F G Fb Fadj)
      (fun b => IsIso.id (G.obj b))

  noncomputable def Pl.unleft_left_adj : Pl.unleft F G Gb Gadj ⊣ Pl.left F G
    := Adjunction.CoreEtaInvertibleHom.mk
      (𝟙 _)
      (fun {a}{o} l =>
        let m : F.obj a ⟶ o.obj.middle := F.map l ≫ inv (o.obj.homl) (I := o.property)
        {
          left := l
          middle := m
          right := (Gadj.homEquiv _ _).invFun (m ≫ o.obj.homr)
          wl := by simp [m,Pl.unleft,OplaxPullbackThing.unleft]
          wr := by simp [m,Pl.unleft,OplaxPullbackThing.unleft] ; sorry -- aesop_cat
        }
      )
      (by
        intro a o f
        simp [Function.LeftInverse,Pl.unleft,OplaxPullbackThing.unleft,Adjunction.CoreEtaInvertibleHom.hom,OplaxPullbackThing.FullSubcategory.leftFunctor,Pl.unleft]
        apply OplaxPullbackThing.Hom.ext
        . simp
        . simp ; sorry
        . simp ; sorry
      )
      sorry

  def unright_right_adj : OplaxPullbackThing.unright F G Fb Fadj ⊣ OplaxPullbackThing.rightFunctor F G
    := sorry

  -- TODO: Something is missing here
  def unincl_pl : OplaxPullbackThing F G ⥤ FullSubcategory (Pl F G) :=
    FullSubcategory.lift
      (Pl F G)
      sorry
      sorry

  def unincl_pr : OplaxPullbackThing F G ⥤ FullSubcategory (Pr F G) := sorry

  instance Pl.reflective : Reflective (fullSubcategoryInclusion (Pl F G)) where
    L := unincl_pl F G
    adj := sorry

  instance Pr.reflective : Reflective (fullSubcategoryInclusion (Pr F G)) where
    L := unincl_pr F G
    adj := sorry

  -- TODO: Can be generalised?
  def Pl.closed_seqColim : ClosedUnderColimitsOfShape ℕ (Pl F G) := sorry
  def Pr.closed_seqColim : ClosedUnderColimitsOfShape ℕ (Pr F G) := sorry

  noncomputable def Plr.reflective : Reflective (fullSubcategoryInclusion (Plr F G))
    := intersectionReflective (Pl F G) (Pr F G) (Pl.closed_seqColim F G) (Pr.closed_seqColim F G)

  noncomputable def Plr.unleft : A ⥤ FullSubcategory (Plr F G)
    := OplaxPullbackThing.unleft F G Gb Gadj ⋙ IntersectionReflective.L (Pl.closed_seqColim F G) (Pr.closed_seqColim F G)

  noncomputable def Plr.unright : B ⥤ FullSubcategory (Plr F G)
    := OplaxPullbackThing.unright F G Fb Fadj ⋙ IntersectionReflective.L (Pl.closed_seqColim F G) (Pr.closed_seqColim F G)

  noncomputable def proj_adj_left : Plr.unleft F G Gb Gadj ⊣ Plr.left F G
    := Adjunction.comp (unleft_left_adj _ _ _ _) (Plr.reflective _ _).adj

  noncomputable def proj_adj_right : Plr.unright F G Fb Fadj ⊣ Plr.right F G
    := Adjunction.comp (unright_right_adj _ _ _ _) (Plr.reflective _ _).adj

end Lemma2

namespace Part3
  universe u
  variable {A : Type _} [Category A] [hsa : HasSeqColimits A]
  variable {B : Type _} [Category B] [hsb : HasSeqColimits B]
  variable (F : C ⥤ A)
  variable (G : C ⥤ B)

  section
  variable (C)
  abbrev Presheaf := Cᵒᵖ ⥤ Type u
  end

  def Fs : Presheaf A ⥤ Presheaf C := sorry -- TODO: restriction of F
  def Gs : Presheaf B ⥤ Presheaf C := sorry
  -- TODO: and then use these with proj_adj_left andproj_adj_right?
  -- TODO: Pullback Fs Gs, then (Presheaf (Pullback Fs Gs) ⥤ A) and (Presheaf (Pullback Fs Gs) ⥤ B)

end Part3

end
