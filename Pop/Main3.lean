import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Monotone.Defs
import Pop.CategoryExtras
import Pop.CategoryTheory.Adjunction.MkExtras
import Pop.CategoryTheory.CommaExtras
import Pop.CategoryTheory.Limits.OplaxPullback
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.CategoryTheory.OplaxPullback
import Pop.CategoryTheory.OplaxPullback.CommaBySubcategory
import Pop.NatCategoryExtras
import Pop.NatExtras

-- set_option pp.proofs true

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

variable {C : Type _} [cc : Category C]
variable {J : Type _} [cj : Category J]
variable [hsc : HasSeqColimits C] -- TODO: Reason for noncomputable. Maybe change later? It seems like most stuff is built on using limit/colimit instead of the cones directly though.
variable (A : Set C)
variable (B : Set C)
variable {unincl_a : C ⥤ FullSubcategory A}
variable {unincl_b : C ⥤ FullSubcategory B}
variable (adj_a : unincl_a ⊣ fullSubcategoryInclusion A)
variable (adj_b : unincl_b ⊣ fullSubcategoryInclusion B)
variable (ca : ClosedUnderColimitsOfShape ℕ A)
variable (cb : ClosedUnderColimitsOfShape ℕ B)
variable [cia : IsClosedUnderIsomorphisms A]
variable [cib : IsClosedUnderIsomorphisms B]
omit [_]

-- TODO: Rename stuff when the proof is finished
namespace IntersectionReflective
  def sequence : Limits.Seq (C ⥤ C) :=
    let TA := adj_a.toMonad
    let TB := adj_b.toMonad
    Seq.iterate2 (c := Cat.of C) (.mk TA.toFunctor TA.η) (.mk TB.toFunctor TB.η)

  section include C cc A B unincl_a unincl_b adj_a adj_b
  lemma sequence_odd {n} : ∀{c}, A (((sequence A B adj_a adj_b).obj (n * 2 + 1)).obj c) := by
    induction n
    . exact FullSubcategory.property _
    . rw [Nat.add_mul]
      intro
      apply_assumption
  lemma sequence_even {n} : ∀{c}, B (((sequence A B adj_a adj_b).obj (n * 2 + 2)).obj c) := sequence_odd B A adj_b adj_a
  end

  noncomputable abbrev Minf : C ⥤ C := colimit (sequence A B adj_a adj_b).diagram
  notation "M∞" => Minf

  variable {A B}

  section include C cc A B unincl_a unincl_b adj_a adj_b hsc cia ca
  lemma Minf_in_left (c : C) : A ((M∞ A B adj_a adj_b).obj c) := by
    apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
    apply IsClosedUnderIsomorphisms.of_iso (Nat.StrictMono.comp_seqColim_iso (·*2+1) (StrictMono.add_const (StrictMono.mul_const strictMono_id (by decide)) _))
    apply ClosedUnderColimitsOfShape.colimit ca
    intro
    apply sequence_odd
  end

  section include C cc A B unincl_a unincl_b adj_a adj_b hsc cib cb
  lemma Minf_in_right (c : C) : B ((M∞ A B adj_a adj_b).obj c) := by
    apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
    apply IsClosedUnderIsomorphisms.of_iso (Nat.StrictMono.comp_seqColim_iso (·*2+2) (StrictMono.add_const (StrictMono.mul_const strictMono_id (by decide)) _))
    apply ClosedUnderColimitsOfShape.colimit cb
    intro
    apply sequence_even
  end

  noncomputable abbrev reflector : C ⥤ FullSubcategory (A ∩ B : Set C) :=
    FullSubcategory.lift
      (A ∩ B : Set C)
      (M∞ A B adj_a adj_b)
      (fun c => .intro (Minf_in_left adj_a adj_b ca c) (Minf_in_right adj_a adj_b cb c))

  -- TODO: Inverse to (sequence A B).map n ?
  -- let test {n} : (sequence A B).obj n.succ ⟶ (sequence A B).obj n := by
  --   simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r]
  --   sorry

  -- TODO: Possible generalisation from the meeting: _ {c a} (cmem : c ∈ A ∩ B) (f : a ⟶ c) : (M∞ A B).obj a ⟶ c
  noncomputable abbrev l' {c} (cmem : c ∈ A ∩ B) : (M∞ A B adj_a adj_b).obj c ⟶ c :=
    let base := adj_a.counit.app ((FullSubcategory.map fun _ => And.left).obj (.mk c cmem))
    let F := (sequence A B adj_a adj_b).diagram.flip.obj c
    let F' := (sequence A B adj_a adj_b).diagram.flip.map base
    let convF : (M∞ A B adj_a adj_b).obj c ⟶ colimit F := ((colimitIsoFlipCompColim (sequence A B adj_a adj_b).diagram).app c).hom
    let h : (n : ℕ) → F.obj n ⟶ c := Nat.rec (𝟙 c) fun n r => sorry ≫ r -- (by simp [F,sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r] ; sorry)
    let Eh : colimit F ⟶ c := colimit.desc F (.mk c $ NatTrans.ofSequence h sorry)
    convF ≫ Eh

  noncomputable def adjunction : reflector adj_a adj_b ca cb ⊣ fullSubcategoryInclusion (A ∩ B : Set C)
    := .mk
      (seqColim.ι (IntersectionReflective.sequence A B adj_a adj_b) 0)
      sorry
      sorry
    -- := Adjunction.CoreEtaInvertibleHom.mk
    --   (seqColim.ι (IntersectionReflective.sequence A B) 0)
    --   (fun f => (reflector ca cb).map f ≫ IntersectionReflective.l''.app _)
    --   (fun f => sorry)
    --   (fun f => sorry)

end IntersectionReflective

namespace Lemma2
  variable {A : Type _} [Category A] [hsa : HasSeqColimits A] [pua : HasPushouts A] [inita : HasInitial A]
  variable {B : Type _} [Category B] [hsb : HasSeqColimits B] [pub : HasPushouts B] [initb : HasInitial B]
  variable [initc : HasInitial C]
  variable (F : A ⥤ C) [pnf : PreservesColimitsOfShape ℕ F]
  variable (G : B ⥤ C) [png : PreservesColimitsOfShape ℕ G]
  variable (Fb : C ⥤ A)
  variable (Gb : C ⥤ B)
  variable (Fadj : Fb ⊣ F)
  variable (Gadj : Gb ⊣ G)

  def Pl  : Set (OplaxPullback F G) := OplaxPullback.CommaLeft F G
  def Pr  : Set (OplaxPullback F G) := OplaxPullback.CommaRight F G
  def Plr : Set (OplaxPullback F G) := (Pl F G) ∩ (Pr F G) -- Pullback.

  abbrev Plr.left  : FullSubcategory (Plr F G) ⥤ A := fullSubcategoryInclusion _ ⋙ OplaxPullback.projLeft _ _
  abbrev Plr.right : FullSubcategory (Plr F G) ⥤ B := fullSubcategoryInclusion _ ⋙ OplaxPullback.projRight _ _

  def OplaxPullback.unleft : A ⥤ OplaxPullback F G
    := OplaxPullback.liftL
      (𝟭 A)
      (F ⋙ Gb)
      ((Functor.leftUnitor F).hom ≫ (Functor.rightUnitor F).inv ≫ whiskerLeft F Gadj.unit ≫ (Functor.associator F Gb G).inv)

  def OplaxPullback.unright : B ⥤ OplaxPullback F G
    := OplaxPullback.liftR
      (G ⋙ Fb)
      (𝟭 B)
      ((Functor.leftUnitor G).hom ≫ (Functor.rightUnitor G).inv ≫ whiskerLeft G Fadj.unit ≫ (Functor.associator G Fb F).inv)

  def Pl.unleft : A ⥤ FullSubcategory (Pl F G)
    := FullSubcategory.lift
      (Pl F G)
      (OplaxPullback.unleft F G Gb Gadj)
      (fun a => IsIso.id (F.obj a))

  def Pr.unright : B ⥤ FullSubcategory (Pr F G)
    := FullSubcategory.lift
      (Pr F G)
      (OplaxPullback.unright F G Fb Fadj)
      (fun b => IsIso.id (G.obj b))

  def Comma.unfst : A ⥤ Comma F G
    := Comma.lift
      (𝟭 A)
      (F ⋙ Gb)
      ((Functor.leftUnitor F).hom ≫ (Functor.rightUnitor F).inv ≫ whiskerLeft F Gadj.unit ≫ (Functor.associator F Gb G).inv)

  def Comma.unfst_fst_adj : Comma.unfst F G Gb Gadj ⊣ Comma.fst F G
    := Adjunction.CoreEtaInvertibleHom.mk
      (𝟙 (𝟭 A))
      (fun {a}{o} l =>
        {
          left := l
          right := (Gadj.homEquiv _ _).invFun (F.map l ≫ o.hom)
          w := by simp [Comma.unfst,Comma.lift,Adjunction.homEquiv]
        }
      )
      (by
        intro a o f
        simp [Function.LeftInverse,OplaxPullback.unleft,Adjunction.CoreEtaInvertibleHom.hom]
        apply CommaMorphism.ext
        . simp
        . simp [Comma.unfst,Comma.lift,Adjunction.homEquiv]
      )
      (by simp [Function.LeftInverse,Function.RightInverse,Adjunction.CoreEtaInvertibleHom.hom])

  @[simps!]
  noncomputable def OplaxPullback.to_comma : OplaxPullback F G ⥤ Comma F G where
    obj o := {
      left   := o.left
      right  := pushout (X := Gb.obj o.middle) (Y := Gb.obj (F.obj o.left)) (Z := o.right) (Gb.map o.homl) ((Gadj.homEquiv _ _).invFun o.homr)
      hom    := Gadj.unit.app (F.obj o.left) ≫ G.map (pushout.inl _ _)
    }
    map f := {
      left := f.left
      right := pushout.map _ _ _ _ (Gb.map (F.map f.left)) (f.right) (Gb.map f.middle)
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

  -- TODO: Maybe "lift" the adjunction to the category of (A ⥤ ·) instead?
  -- So instead of (Gb ⊣ G) where Gb : C ⥤ B , G: B ⥤ C, something like:
  -- ((A ⥤ C) ⥤ (A ⥤ B)) and ((A ⥤ B) ⥤ (A ⥤ C)) stating that these are also adjoint?
  def test {X : A ⥤ C} {Y : A ⥤ B}
    (adj : Gb ⊣ G) (f : X ⟶ Y ⋙ G)
    : X ⋙ Gb ⟶ Y
    where
    app a := (Adjunction.homEquiv adj _ _).invFun (f.app a)
    naturality :=
      -- let test := Over.post (T := Cat) (D := sorry) (X := Cat.of A) G
      sorry

  noncomputable def OplaxPullback.to_comma' : OplaxPullback F G ⥤ Comma F G
    := Comma.lift
      (OplaxPullback.projLeft _ _)
      (pushout
        (X := OplaxPullback.projMid _ _ ⋙ Gb)
        (Y := OplaxPullback.projLeft _ _ ⋙ F ⋙ Gb)
        (Z := OplaxPullback.projRight _ _)
        (whiskerRight (OplaxPullback.llm _ _) Gb)
        (test G Gb Gadj (OplaxPullback.rrm _ _))
      )
      ( (Functor.rightUnitor _ ).inv
      ≫ whiskerLeft (OplaxPullback.projLeft F G ⋙ F) Gadj.unit
      ≫ sorry -- whiskerRight sorry G
      )

  noncomputable def OplaxPullback.to_from_comma_adj : OplaxPullback.to_comma F G Gb Gadj ⊣ OplaxPullback.from_comma F G where
    unit := {
      app o := {
        left := 𝟙 _
        middle := o.homl
        right := pushout.inr _ _
        wl := by
          simp only [Functor.id_obj,CategoryTheory.Functor.map_id,Category.comp_id,Functor.comp_obj,OplaxPullback.from_comma_obj_homl,to_comma_obj_left]
          exact (Category.comp_id _).symm
        wr := by
          simp [Adjunction.homEquiv]
          let cond := congr_arg (Gadj.unit.app o.middle ≫ ·) (congr_arg G.map (pushout.condition (f := Gb.map o.homl) (g := (Gadj.homEquiv _ _).invFun o.homr)))
          simp [Adjunction.homEquiv] at cond
          exact cond.symm
      }
    }
    counit := {
      app o := {
        left := 𝟙 _
        right := pushout.desc
          (Gb.map o.hom ≫ Gadj.counit.app o.right)
          (𝟙 _)
          (by simp [Adjunction.homEquiv])
        w := by
          let eq : Gb.map (𝟙 (F.obj o.left)) ≫ Gb.map o.hom ≫ Gadj.counit.app o.right = (Gb.map o.hom ≫ Gadj.counit.app o.right) ≫ 𝟙 o.right := by simp
          simp [Adjunction.homEquiv] -- TODO: -Functor.map_comp ?
          rw [← Functor.map_comp]
          simp [pushout.inl_desc _ _ eq]
      }
      naturality x y f := by
        ext
        . simp [to_comma,OplaxPullback.from_comma]
        . simp [to_comma,OplaxPullback.from_comma,(·≫·),Adjunction.homEquiv,f.w,pushout.map]
          sorry -- TODO: pushout.desc and composition?
    }
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
    --       let cond := congr_arg (Gadj.unit.app o.middle ≫ ·) (congr_arg G.map (pushout.condition (f := Gb.map o.homl) (g := (Gadj.homEquiv _ _).invFun o.homr)))
    --       simp [Adjunction.homEquiv] at cond
    --       exact cond.symm
    --     }}
    --   (fun {x y} f => by
    --     simp [to_comma,OplaxPullback.from_comma,(·≫·),OplaxPullback.liftL,OplaxPullback.lift,Comma.fst,Comma.snd,Comma.natTrans] at f
    --     exact {
    --       left := f.left
    --       right := pushout.desc
    --         (Gb.map (F.map f.left ≫ y.hom) ≫ Gadj.counit.app _)
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

  noncomputable def OplaxPullback.to_flipped_comma : OplaxPullback F G ⥤ Comma G F
    := OplaxPullback.flip ⋙ OplaxPullback.to_comma G F Fb Fadj

  noncomputable def OplaxPullback.to_from_flipped_comma_adj : OplaxPullback.to_flipped_comma F G Fb Fadj ⊣ OplaxPullback.from_flipped_comma F G
    := by
      rw [← OplaxPullback.from_comma_flip]
      exact Adjunction.comp OplaxPullback.flip_equiv.toAdjunction (OplaxPullback.to_from_comma_adj _ _ _ _)

  noncomputable def OplaxPullback.unprojLeft : A ⥤ OplaxPullback F G where
    obj x := {
      left   := x
      middle := initial C
      right  := initial B
      homl := initial.to _
      homr := initial.to _
    }
    map f := {
      left   := f
      middle := 𝟙 _
      right  := 𝟙 _
    }

  noncomputable def OplaxPullback.unprojRight : B ⥤ OplaxPullback F G where
    obj x := {
      left   := initial A
      middle := initial C
      right  := x
      homl := initial.to _
      homr := initial.to _
    }
    map f := {
      left   := 𝟙 _
      middle := 𝟙 _
      right  := f
    }

  noncomputable def OplaxPullback.unleft_left_functor_adj : OplaxPullback.unprojLeft F G ⊣ OplaxPullback.projLeft F G := by
    dsimp only [unprojLeft,OplaxPullback.projLeft]
    exact {
      unit := 𝟙 _
      counit := {
        app x := {
          left   := 𝟙 _
          middle := initial.to _
          right  := initial.to _
        }
      }
    }

  noncomputable def OplaxPullback.unright_right_functor_adj : OplaxPullback.unprojRight F G ⊣ OplaxPullback.projRight F G := by
    dsimp only [unprojRight,OplaxPullback.projRight]
    exact {
      unit := 𝟙 _
      counit := {
        app x := {
          left   := initial.to _
          middle := initial.to _
          right  := 𝟙 _
        }
      }
    }

  def Pl.unleft' : A ⥤ FullSubcategory (Pl F G)
    := Comma.unfst F G Gb Gadj ⋙ OplaxPullback.CommaLeft.from_comma

  def Pl.unright' : B ⥤ FullSubcategory (Pr F G)
    := Comma.unfst G F Fb Fadj ⋙ OplaxPullback.CommaRight.from_comma

  noncomputable abbrev Pl.left' : FullSubcategory (Pl F G) ⥤ A
    := OplaxPullback.CommaLeft.to_comma ⋙ Comma.fst _ _

  noncomputable abbrev Pl.right' : FullSubcategory (Pr F G) ⥤ B
    := OplaxPullback.CommaRight.to_comma ⋙ Comma.fst _ _

  noncomputable def Pl.unleft_left_adj : Pl.unleft' F G Gb Gadj ⊣ Pl.left' F G
    := Adjunction.comp (Comma.unfst_fst_adj _ _ _ _) OplaxPullback.CommaLeft.equiv_comma.symm.toAdjunction

  noncomputable def Pr.unright_right_adj : Pl.unright' F G Fb Fadj ⊣ Pl.right' F G
    := Adjunction.comp (Comma.unfst_fst_adj _ _ _ _) OplaxPullback.CommaRight.equiv_comma.symm.toAdjunction

  noncomputable def Pl.unincl : OplaxPullback F G ⥤ FullSubcategory (Pl F G)
    := OplaxPullback.to_comma F G Gb Gadj ⋙ OplaxPullback.CommaLeft.from_comma

  noncomputable def Pr.unincl : OplaxPullback F G ⥤ FullSubcategory (Pr F G)
    := OplaxPullback.to_flipped_comma F G Fb Fadj ⋙ OplaxPullback.CommaRight.from_comma

  noncomputable def Pl.unincl_incl_adj : Pl.unincl F G Gb Gadj ⊣ fullSubcategoryInclusion (Pl F G)
    := Adjunction.ofNatIsoRight
      (Adjunction.comp
        (OplaxPullback.to_from_comma_adj F G Gb Gadj)
        OplaxPullback.CommaLeft.equiv_comma.symm.toAdjunction
      )
      OplaxPullback.CommaLeft.to_from_inclusion

  noncomputable def Pr.unincl_incl_adj : Pr.unincl F G Fb Fadj ⊣ fullSubcategoryInclusion (Pr F G)
    := Adjunction.ofNatIsoRight
      (Adjunction.comp
        (OplaxPullback.to_from_flipped_comma_adj F G Fb Fadj)
        OplaxPullback.CommaRight.equiv_comma.symm.toAdjunction
      )
      OplaxPullback.CommaRight.to_from_inclusion

  local instance Pl.closed_iso : IsClosedUnderIsomorphisms (Pl F G)
    := CategoryTheory.natIso_isClosedUnderIso (OplaxPullback.llm F G)
  local instance Pr.closed_iso : IsClosedUnderIsomorphisms (Pr F G)
    := CategoryTheory.natIso_isClosedUnderIso (OplaxPullback.rrm F G)
  local instance [hc : HasSeqColimits C] : HasSeqColimits (OplaxPullback F G)
    := OplaxPullback.hasColimitsOfShape

  def Pl.closed_seqColim [pf : PreservesColimitsOfShape J F] : ClosedUnderColimitsOfShape J (Pl F G) := by
    -- let _ := Pl.closed_iso F G
    -- apply closedUnderColimitsOfShape_of_colimit
    -- intro H h p
    -- let pp := pf.preservesColimit (K := H ⋙ OplaxPullback.projLeft _ _).preserves (c := (OplaxPullback.projLeft F G).mapCocone (getColimitCocone H).cocone) sorry
    -- sorry

    intro H c isc p
    let pp := pf.preservesColimit (K := H ⋙ OplaxPullback.projLeft _ _).preserves (c := (OplaxPullback.projLeft F G).mapCocone c) sorry
    -- simp [Pl,OplaxPullback.CommaLeft]
    -- let test := ClosedUnderColimitsOfShape.essImage sorry
    let t := c.ι.naturality
    dsimp at t
    dsimp [Pl,OplaxPullback.CommaLeft]
    dsimp [Pl,OplaxPullback.CommaLeft] at p
    exact IsClosedUnderIsomorphisms.of_iso (self := Pl.closed_iso F G) sorry (p sorry)

  def Pr.closed_seqColim [pg : PreservesColimitsOfShape J G] : ClosedUnderColimitsOfShape J (Pr F G) := sorry

  noncomputable def Plr.unincl : OplaxPullback F G ⥤ FullSubcategory (Plr F G)
    := IntersectionReflective.reflector
      (Pl.unincl_incl_adj F G Gb Gadj)
      (Pr.unincl_incl_adj F G Fb Fadj)
      (Pl.closed_seqColim F G)
      (Pr.closed_seqColim F G)
      (cia := Pl.closed_iso F G) -- TODO: Cannot find instances?
      (cib := Pr.closed_iso F G)

  noncomputable def Plr.unincl_incl_adj : Plr.unincl F G Fb Gb Fadj Gadj ⊣ fullSubcategoryInclusion (Plr F G)
    := IntersectionReflective.adjunction
      (Pl.unincl_incl_adj F G Gb Gadj)
      (Pr.unincl_incl_adj F G Fb Fadj)
      (Pl.closed_seqColim F G)
      (Pr.closed_seqColim F G)
      (cia := Pl.closed_iso F G)
      (cib := Pr.closed_iso F G)

  noncomputable def Plr.unleft : A ⥤ FullSubcategory (Plr F G)
    := OplaxPullback.unprojLeft F G ⋙ Plr.unincl F G Fb Gb Fadj Gadj

  noncomputable def Plr.unright : B ⥤ FullSubcategory (Plr F G)
    := OplaxPullback.unprojRight F G ⋙ Plr.unincl F G Fb Gb Fadj Gadj

  noncomputable def Plr.unleft_left_adj : Plr.unleft F G Fb Gb Fadj Gadj ⊣ Plr.left F G
    := Adjunction.comp (OplaxPullback.unleft_left_functor_adj _ _) (Plr.unincl_incl_adj _ _ _ _ _ _)

  noncomputable def Plr.unright_right_adj : Plr.unright F G Fb Gb Fadj Gadj ⊣ Plr.right F G
    := Adjunction.comp (OplaxPullback.unright_right_functor_adj _ _) (Plr.unincl_incl_adj _ _ _ _ _ _)

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
  def Gs : Presheaf B ⥤ Presheaf C := sorry -- TODO: Stated that these are just whiskerings on the meeting, but...
  -- TODO: and then use these with proj_adj_left andproj_adj_right?
  -- TODO: Pullback Fs Gs, then (Presheaf (Pullback Fs Gs) ⥤ A) and (Presheaf (Pullback Fs Gs) ⥤ B)

end Part3
