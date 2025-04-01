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

set_option pp.proofs true

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

def fullSubcategoryMonad := (reflectorAdjunction (fullSubcategoryInclusion A)).toMonad

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

  noncomputable abbrev L := FullSubcategory.lift
    (A ∩ B : Set C)
    (M∞ A B)
    (fun c => .intro (Minf_in_left closed_a c) (Minf_in_right closed_b c))

  noncomputable abbrev l : M∞ A B ⟶ 𝟭 C :=
    let ta' : (sequence A B).obj 1 ⟶ (sequence A B).obj 0 := by -- TODO: ?
      simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r,fullSubcategoryMonad] -- fullSubcategoryInclusion,inducedFunctor,FullSubcategory.obj,reflector
      let te := (reflectorAdjunction (fullSubcategoryInclusion A)).counit
      sorry

    -- TODO: Inverse to (sequence A B).map n ?
    let test {n} : (sequence A B).obj n.succ ⟶ (sequence A B).obj n := by
      simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r]
      sorry

    colimit.desc
      (sequence A B).diagram
      (.mk (𝟭 C) (NatTrans.ofSequence
        (Nat.rec (𝟙 (𝟭 C)) (fun _ => (test ≫·)))
        (by
          intro n
          simp
          sorry
        )
      ))

  noncomputable abbrev l' {c} : (M∞ A B).obj c ⟶ c :=
    let F := (sequence A B).diagram.flip.obj c
    let convF : (M∞ A B).obj c ⟶ colimit F := ((colimitIsoFlipCompColim (sequence A B).diagram).app c).hom
    let h : (n : ℕ) → F.obj n ⟶ c := Nat.rec (𝟙 c) fun n r => sorry ≫ r
    let Eh : colimit F ⟶ c := colimit.desc F (.mk c $ NatTrans.ofSequence h sorry)
    convF ≫ Eh

end IntersectionReflective

noncomputable def intersectionReflective : Reflective (fullSubcategoryInclusion (A ∩ B : Set C)) :=
  let L := IntersectionReflective.L closed_a closed_b
  {
    L := L
    adj := Adjunction.CoreEtaInvertibleHom.mk
      (seqColim.ι (IntersectionReflective.sequence A B) 0)
      (fun f => L.map f ≫ IntersectionReflective.l') -- TODO: or IntersectionReflective.l.app _
      (fun f => sorry)
      (fun f => sorry)
  }

namespace Lemma2
  variable {A : Type _} [Category A] [hsa : HasSeqColimits A]
  variable {B : Type _} [Category B] [hsb : HasSeqColimits B]
  variable (F : A ⥤ C)
  variable (G : B ⥤ C)
  variable (Fb : C ⥤ A)
  variable (Gb : C ⥤ B)
  variable (Fb : Fb ⊣ F)
  variable (Gb : Gb ⊣ G)
  variable (pua : HasPushouts A)
  variable (pub : HasPushouts B)
  variable (pnf : PreservesColimitsOfShape ℕ F)
  variable (png : PreservesColimitsOfShape ℕ G)

  def Pl  : Set (OplaxPullbackThing F G) := fun p => IsIso p.homl
  def Pr  : Set (OplaxPullbackThing F G) := fun p => IsIso p.homr
  def Plr : Set (OplaxPullbackThing F G) := (Pl F G) ∩ (Pr F G)

  def comma_pl : Comma F G ⥤ FullSubcategory (Pl F G)
    := FullSubcategory.lift (Pl F G) (OplaxPullbackThing.byComma F G) (by simp [OplaxPullbackThing.byComma,Pl] ; infer_instance)

  def comma_pr : Comma G F ⥤ FullSubcategory (Pr F G)
    := FullSubcategory.lift (Pr F G) (OplaxPullbackThing.byFlippedComma F G) (by simp [OplaxPullbackThing.byFlippedComma,Pr] ; infer_instance)

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

  -- TODO: Maybe there is an easier way
  instance Pl_closed_iso : IsClosedUnderIsomorphisms (Pl F G) := sorry
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
  instance Pr_closed_iso : IsClosedUnderIsomorphisms (Pr F G) := sorry

  instance Pl_refl : Reflective (fullSubcategoryInclusion (Pl F G)) := sorry
  instance Pr_refl : Reflective (fullSubcategoryInclusion (Pr F G)) := sorry

  local instance [hc : HasSeqColimits C] : HasSeqColimits (OplaxPullbackThing F G)
    := sorry
    -- := OplaxPullbackThing.hasColimitsOfShape

  def Pl_closed_seqColim : ClosedUnderColimitsOfShape ℕ (Pl F G) := sorry
  def Pr_closed_seqColim : ClosedUnderColimitsOfShape ℕ (Pr F G) := sorry

  noncomputable def Plr_refl : Reflective (fullSubcategoryInclusion (Plr F G))
    := intersectionReflective (Pl F G) (Pr F G) (Pl_closed_seqColim F G) (Pr_closed_seqColim F G)

  def proj_a : FullSubcategory (Plr F G) ⥤ A := sorry
  def proj_b : FullSubcategory (Plr F G) ⥤ B := sorry

  -- TODO: By compositions of adjunctions
  def unproj_a : A ⥤ FullSubcategory (Plr F G) := sorry
  def unproj_b : B ⥤ FullSubcategory (Plr F G) := sorry

  def proj_adj_left : unproj_a F G ⊣ proj_a F G := sorry
  def proj_adj_right : unproj_b F G ⊣ proj_b F G := sorry

end Lemma2

namespace FutureTODOs
  variable {A : Type _} [Category A] [hsa : HasSeqColimits A]
  variable {B : Type _} [Category B] [hsb : HasSeqColimits B]
  variable (F : C ⥤ A)
  variable (G : C ⥤ B)

  -- Presheaf C := Cᵒᵖ ⥤ ?

  -- def Fs : Presheaf A ⥤ Presheaf C
  -- def Gs : Presheaf A ⥤ Presheaf C
  -- TODO: and then use these with proj_adj_left andproj_adj_right?
  -- TODO: Pullback Fs Gs, then (Presheaf (Pullback Fs Gs) ⥤ A) and (Presheaf (Pullback Fs Gs) ⥤ B)

end FutureTODOs

end
