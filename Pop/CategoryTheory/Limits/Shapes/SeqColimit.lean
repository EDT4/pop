import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Monad.Limits

-- TODO: Lookup cofiltered category and tower diagrams
-- TODO: Sources:
--   https://who.rocq.inria.fr/Kristina.Sojakova/papers/sequential_colimits_homotopy.pdf
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/OfSequence.html
-- Follows the structure of https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.html
namespace CategoryTheory.Limits

open CategoryTheory
open CategoryTheory.Limits

universe v u
variable {C : Type u}
variable [Category.{v, u} C]

abbrev SeqDiagram (C : Type u) [Category.{v, u} C] := Functor ℕ C

abbrev HasSeqColimit(f : SeqDiagram C) := HasColimit f
noncomputable abbrev seqColim (f : SeqDiagram C) [HasSeqColimit f] := colimit f

noncomputable abbrev seqColim.ι (f : SeqDiagram C) [HasSeqColimit f] (n : ℕ)
  : f.obj n ⟶ seqColim f
  := colimit.ι f n



structure Seq (C : Type u) [Category.{v, u} C] where
  obj : ℕ → C
  map : (n : ℕ) → obj n ⟶ obj (Nat.succ n)

abbrev Seq.step (s : Seq C) : Seq C := .mk (s.obj ∘ Nat.succ) (fun n => s.map (Nat.succ n))

def SeqDiagram.bySequence (s : Seq C) : SeqDiagram C
  := Functor.ofSequence s.map

namespace BySequence
  variable {W : C}
  variable (s : Seq C)
  variable {p : (n : ℕ) → s.obj n ⟶ W}
  variable {eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n}

  lemma map_id (n : ℕ) (o : n ⟶ n) : (SeqDiagram.bySequence s).map o = CategoryStruct.id (s.obj n)
    := by
      rewrite [Subsingleton.elim o (homOfLE (by omega))]
      exact Functor.OfSequence.map_id s.map n

  lemma map_comp (a b c : ℕ) (o1 : a ⟶ b) (o2 : b ⟶ c) (o3 : a ⟶ c) : (SeqDiagram.bySequence s).map o3 = (SeqDiagram.bySequence s).map o1 ≫ (SeqDiagram.bySequence s).map o2
    := Functor.OfSequence.map_comp s.map a b c (leOfHom o1) (leOfHom o2)

  lemma map_succ (n : ℕ) (o : n ⟶ Nat.succ n) : (SeqDiagram.bySequence s).map o = s.map n
    := by
      rewrite [Subsingleton.elim o (homOfLE (Nat.le_add_right n 1))]
      exact Functor.OfSequence.map_le_succ s.map n

  -- Follows the structure of https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.html
  abbrev SeqColimCocone := Cocone (SeqDiagram.bySequence s)
  namespace SeqColimCocone
    variable {s : Seq C}
    variable {t : SeqColimCocone s}

    -- TODO: This is probably the correct signature
    -- def mk2 (s' : Seq C)
    --   (p : (n : ℕ) → s.obj n ⟶ s'.obj n)
    --   (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n ≫ s'.map n)
    --   : SeqColimCocone s
    --   := sorry

    def mk
      (p : (n : ℕ) → s.obj n ⟶ W) -- TODO: Is it really enough when W is not dependent on n?
      (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
      : SeqColimCocone s where
      pt := W
      ι :=
        let e := by
          intro n
          simp
          rewrite [map_succ s n (homOfLE (by omega))]
          exact eq n
        NatTrans.ofSequence (F := SeqDiagram.bySequence s) (G := (Functor.const ℕ).obj W) p e

    abbrev ι (t : SeqColimCocone s) (n : ℕ) : s.obj n ⟶ t.pt
      := (Cocone.ι t).app n

    @[reassoc]
    theorem condition (n : ℕ)
      : s.map n ≫ ι t (Nat.succ n) = ι t n
      := by
        let o : n ⟶ Nat.succ n := homOfLE (by omega)
        rewrite [(map_succ s n o).symm]
        exact Cocone.w t o

    def step (t : SeqColimCocone s)
      : SeqColimCocone s.step
      := SeqColimCocone.mk
        (fun n => t.ι (Nat.succ n))
        (fun n => t.condition (Nat.succ n))

    def unstep (t : SeqColimCocone s.step)
      : SeqColimCocone s
      := SeqColimCocone.mk
        (fun n => s.map n ≫ SeqColimCocone.ι t n)
        (fun n => by simp ; rewrite [t.condition n] ; rfl)

    def stepIsColimit (ht : IsColimit t) : IsColimit t.step
      := IsColimit.mk
        (fun s => ht.desc (unstep s))
        (fun s j => by simp ; sorry) -- TODO: How to unroll the definitions?
        (fun s m j => by simp ; sorry)
        -- IsColimit.mk _ (fun s => ht.desc s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by apply IsColimit.hom_ext ht <;> simp [h₁, h₂])

  end SeqColimCocone

  noncomputable abbrev seqColim.cocone
    [HasSeqColimit (SeqDiagram.bySequence s)]
    := colimit.cocone (SeqDiagram.bySequence s)

  noncomputable abbrev seqColim.desc
    [HasSeqColimit (SeqDiagram.bySequence s)]
    (p : (n : ℕ) → s.obj n ⟶ W)
    (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
    : seqColim (SeqDiagram.bySequence s) ⟶ W
    := colimit.desc (SeqDiagram.bySequence s) (SeqColimCocone.mk p eq)

  @[reassoc]
  theorem seqColim.ι_desc
    [HasSeqColimit (SeqDiagram.bySequence s)]
    (p : (n : ℕ) → s.obj n ⟶ W)
    (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
    (n : ℕ)
    : seqColim.ι _ n ≫ seqColim.desc s p eq = p n
    := colimit.ι_desc _ _

  @[reassoc]
  theorem seqColim.condition
    [HasSeqColimit (SeqDiagram.bySequence s)]
    (n : ℕ)
    : s.map n ≫ seqColim.ι (SeqDiagram.bySequence s) (Nat.succ n) = seqColim.ι (SeqDiagram.bySequence s) n
    := SeqColimCocone.condition n

  -- def seqColimIsSeqColim
  --   [HasSeqColimit (SeqDiagram.bySequence s)]
  --   : IsColimit (SeqColimCocone.mk (seqColim.ι) seqColim.condition)
  --   := SeqColimCocone.IsColimit.mk _ (fun s => seqColim.desc s.ι s.condition) (by simp) (by simp) (by aesop_cat)
  --
  -- instance hasSeqColimit_step [HasSeqColimit (SeqDiagram.bySequence s)]
  --   : HasSeqColimit (SeqDiagram.bySequence s.step) -- TODO: Where is the dependent function composition?
  --   := ⟨⟨⟨_, SeqColimCocone.stepIsColimit (seqColimIsSeqColim s)⟩⟩⟩
  --
  -- def seqColim_step
  --   [HasSeqColimit (SeqDiagram.bySequence s)]
  --   : seqColim (SeqDiagram.bySequence s) ≅ seqColim (SeqDiagram.bySequence s.step)
  --   := IsColimit.coconePointUniqueUpToIso (SeqColimCocone.stepIsColimit (seqColimIsSeqColim s)) (colimit.isColimit _)

end BySequence



def SeqDiagram.byRepeat (f : Functor C C) (z : Σ c : C, c ⟶ f.obj c) : SeqDiagram C :=
  let o (n : ℕ) : C := Nat.repeat f.obj n z.1
  let rec m (n : ℕ) : o n ⟶ o (n + 1) := match n with
    | Nat.zero   => z.2
    | Nat.succ n => f.map (m n)
  SeqDiagram.bySequence (.mk o m)



-- TODO: Pointed endofunctor (NatTrans (Functor.id C) f) instead of zm, but what would the naturality give?
def SeqDiagram.byRepeat' (f : Functor C C) (m : NatTrans (Functor.id C) f) (z : C) : SeqDiagram C :=
  SeqDiagram.byRepeat f (.mk z (m.app z))

end Limits
