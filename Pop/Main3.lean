import Mathlib.CategoryTheory.Adjunction.Whiskering
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
import Pop.CategoryTheory.Adjunction.Comma
import Pop.CategoryTheory.Adjunction.MkExtras
import Pop.CategoryTheory.Adjunction.OplaxPullback
import Pop.CategoryTheory.Adjunction.OplaxPullback.Comma
import Pop.CategoryTheory.Adjunction.OplaxPullback.CommaSubcategory
import Pop.CategoryTheory.CommaExtras
import Pop.CategoryTheory.Limits.OplaxPullback
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.CategoryTheory.OplaxPullback
import Pop.CategoryTheory.OplaxPullback.CommaSubcategory
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
-- CategoryTheory.Limits.pointwiseCocone
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
  variable (L : A ⥤ C) [pnl : PreservesColimitsOfShape ℕ L]
  variable (R : B ⥤ C) [pnr : PreservesColimitsOfShape ℕ R]
  variable (Lb : C ⥤ A)
  variable (Rb : C ⥤ B)
  variable (Ladj : Lb ⊣ L)
  variable (Radj : Rb ⊣ R)

  def Pl  : Set (OplaxPullback L R) := OplaxPullback.CommaLeft L R
  def Pr  : Set (OplaxPullback L R) := OplaxPullback.CommaRight L R
  def Plr : Set (OplaxPullback L R) := (Pl L R) ∩ (Pr L R) -- Pullback.

  abbrev Plr.left  : FullSubcategory (Plr L R) ⥤ A := fullSubcategoryInclusion _ ⋙ OplaxPullback.projLeft _ _
  abbrev Plr.right : FullSubcategory (Plr L R) ⥤ B := fullSubcategoryInclusion _ ⋙ OplaxPullback.projRight _ _

  def Pl.closed_seqColim
    [pf : PreservesColimitsOfShape J L]
    : ClosedUnderColimitsOfShape J (Pl L R)
    := by
      intro F cf iscf p

      let P := FullSubcategory.lift (Pl L R) F p

      -- TODO: Move to CategoryTheory.Limits.OplaxPullback.CommaSubcategory
      let coconePrecompose_mll
        (c : Cocone (P ⋙ OplaxPullback.CommaLeft.projMid L R))
        : Cocone (P ⋙ OplaxPullback.CommaLeft.projLeft L R ⋙ L)
        := (Cocones.precompose (whiskerLeft P (OplaxPullback.CommaLeft.mll L R))).obj c

      let res
        (cl : Cocone (P ⋙ OplaxPullback.CommaLeft.projLeft L R)) (tl : IsColimit cl)
        (cm : Cocone (P ⋙ OplaxPullback.CommaLeft.projMid  L R))
        : L.obj cl.pt ⟶ cm.pt
        := (pf.preservesColimit.preserves tl).some.desc (coconePrecompose_mll cm)

      exact .mk $ .intro
        (res
          ((OplaxPullback.projLeft L R).mapCocone cf)
          sorry -- TODO: explicitly?
          ((OplaxPullback.projMid L R).mapCocone cf)
        )
        (by
          simp only [res,P,coconePrecompose_mll]
          constructor
          · sorry
          · sorry
        )

  def Pr.closed_seqColim [pg : PreservesColimitsOfShape J R] : ClosedUnderColimitsOfShape J (Pr L R) := by
    let t := Pl.closed_seqColim (L := R) (R := L) (pf := pg)
    unfold Pl at t
    unfold Pr OplaxPullback.CommaRight
    sorry -- TODO: copy and generalise from Pl.closed_seqColim later instead of proving stuff about flip

  local instance [hc : HasSeqColimits C] : HasSeqColimits (OplaxPullback L R)
    := OplaxPullback.hasColimitsOfShape

  noncomputable def Plr.unincl : OplaxPullback L R ⥤ FullSubcategory (Plr L R)
    := IntersectionReflective.reflector
      (OplaxPullback.CommaLeft.unincl_incl_adj L R Rb Radj)
      (OplaxPullback.CommaRight.unincl_incl_adj L R Lb Ladj)
      (Pl.closed_seqColim L R)
      (Pr.closed_seqColim L R)
      (cia := OplaxPullback.CommaLeft.closed_iso) -- TODO: Cannot find instances?
      (cib := OplaxPullback.CommaRight.closed_iso)

  noncomputable def Plr.unincl_incl_adj : Plr.unincl L R Lb Rb Ladj Radj ⊣ fullSubcategoryInclusion (Plr L R)
    := IntersectionReflective.adjunction
      (OplaxPullback.CommaLeft.unincl_incl_adj L R Rb Radj)
      (OplaxPullback.CommaRight.unincl_incl_adj L R Lb Ladj)
      (Pl.closed_seqColim L R)
      (Pr.closed_seqColim L R)
      (cia := OplaxPullback.CommaLeft.closed_iso)
      (cib := OplaxPullback.CommaRight.closed_iso)

  noncomputable def Plr.unleft : A ⥤ FullSubcategory (Plr L R)
    := OplaxPullback.OfInitial.unprojLeft L R ⋙ Plr.unincl L R Lb Rb Ladj Radj

  noncomputable def Plr.unright : B ⥤ FullSubcategory (Plr L R)
    := OplaxPullback.OfInitial.unprojRight L R ⋙ Plr.unincl L R Lb Rb Ladj Radj

  noncomputable def Plr.unleft_left_adj : Plr.unleft L R Lb Rb Ladj Radj ⊣ Plr.left L R
    := Adjunction.comp (OplaxPullback.OfInitial.projLeft_adj _ _) (Plr.unincl_incl_adj _ _ _ _ _ _)

  noncomputable def Plr.unright_right_adj : Plr.unright L R Lb Rb Ladj Radj ⊣ Plr.right L R
    := Adjunction.comp (OplaxPullback.OfInitial.projRight_adj _ _) (Plr.unincl_incl_adj _ _ _ _ _ _)

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
