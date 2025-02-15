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



def SeqDiagram.bySequence (f : ℕ → C) (m : (n : ℕ) → f n ⟶ f (Nat.succ n)) : SeqDiagram C
  := Functor.ofSequence m

namespace BySequence
  variable {W : C}
  variable (so : ℕ → C)
  variable (sm : (n : ℕ) → so n ⟶ so (Nat.succ n))
  variable {p : (n : ℕ) → so n ⟶ W}
  variable {eq : ∀(n : ℕ), sm n ≫ p (Nat.succ n) = p n}

  lemma map_id (n : ℕ) (o : n ⟶ n) : (SeqDiagram.bySequence so sm).map o = CategoryStruct.id (so n)
    := by
      rewrite [Subsingleton.elim o (homOfLE (by omega))]
      exact Functor.OfSequence.map_id sm n

  lemma map_comp (a b c : ℕ) (o1 : a ⟶ b) (o2 : b ⟶ c) (o3 : a ⟶ c) : (SeqDiagram.bySequence so sm).map o3 = (SeqDiagram.bySequence so sm).map o1 ≫ (SeqDiagram.bySequence so sm).map o2
    := Functor.OfSequence.map_comp sm a b c (leOfHom o1) (leOfHom o2)

  lemma map_succ (n : ℕ) (o : n ⟶ Nat.succ n) : (SeqDiagram.bySequence so sm).map o = sm n
    := by
      rewrite [Subsingleton.elim o (homOfLE (Nat.le_add_right n 1))]
      exact Functor.OfSequence.map_le_succ sm n

  -- Follows the structure of https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.html
  abbrev SeqColimCocone := Cocone (SeqDiagram.bySequence so sm)
  namespace SeqColimCocone
    variable {so : ℕ → C}
    variable {sm : (n : ℕ) → so n ⟶ so (Nat.succ n)}
    variable {t : SeqColimCocone so sm}

    def mk
      (p : (n : ℕ) → so n ⟶ W)
      (eq : ∀(n : ℕ), sm n ≫ p (Nat.succ n) = p n)
      : SeqColimCocone so sm where
      pt := W
      ι :=
        let e := by
          intro n
          simp
          rewrite [map_succ so sm n (homOfLE (by omega))]
          exact eq n
        NatTrans.ofSequence (F := SeqDiagram.bySequence so sm) (G := (Functor.const ℕ).obj W) p e

    abbrev ι (t : SeqColimCocone so sm) (n : ℕ) : so n ⟶ t.pt
      := (Cocone.ι t).app n

    @[reassoc]
    theorem condition (n : ℕ)
      : sm n ≫ ι t (Nat.succ n) = ι t n
      := by
        let o : n ⟶ Nat.succ n := homOfLE (by omega)
        rewrite [(map_succ so sm n o).symm]
        exact Cocone.w t o
  end SeqColimCocone

  noncomputable abbrev seqColim.cocone
    [HasSeqColimit (SeqDiagram.bySequence so sm)]
    := colimit.cocone (SeqDiagram.bySequence so sm)

  noncomputable abbrev seqColim.desc
    [HasSeqColimit (SeqDiagram.bySequence so sm)]
    (p : (n : ℕ) → so n ⟶ W)
    (eq : ∀(n : ℕ), sm n ≫ p (Nat.succ n) = p n)
    : seqColim (SeqDiagram.bySequence so sm) ⟶ W
    := colimit.desc (SeqDiagram.bySequence so sm) (SeqColimCocone.mk p eq)

  @[reassoc]
  theorem seqColim.ι_desc
    [HasSeqColimit (SeqDiagram.bySequence so sm)]
    (p : (n : ℕ) → so n ⟶ W)
    (eq : ∀(n : ℕ), sm n ≫ p (Nat.succ n) = p n)
    (n : ℕ)
    : seqColim.ι _ n ≫ seqColim.desc so sm p eq = p n
    := colimit.ι_desc _ _

  @[reassoc]
  theorem seqColim.condition
    [HasSeqColimit (SeqDiagram.bySequence so sm)]
    (n : ℕ)
    : sm n ≫ seqColim.ι (SeqDiagram.bySequence so sm) (Nat.succ n) = seqColim.ι (SeqDiagram.bySequence so sm) n
    := SeqColimCocone.condition n

end BySequence



def SeqDiagram.byRepeat (f : Functor C C) (z : Σ c : C, c ⟶ f.obj c) : SeqDiagram C :=
  let o (n : ℕ) : C := Nat.repeat f.obj n z.1
  let rec m (n : ℕ) : o n ⟶ o (n + 1) := match n with
    | Nat.zero   => z.2
    | Nat.succ n => f.map (m n)
  SeqDiagram.bySequence o m



-- TODO: Pointed endofunctor (NatTrans (Functor.id C) f) instead of zm, but what would the naturality give?
def SeqDiagram.byRepeat' (f : Functor C C) (m : NatTrans (Functor.id C) f) (z : C) : SeqDiagram C :=
  SeqDiagram.byRepeat f (.mk z (m.app z))

end Limits
