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

structure Seq (C : Type u) [Category.{v, u} C] where
  obj : ℕ → C
  map : (n : ℕ) → obj n ⟶ obj (Nat.succ n)
namespace Seq
  abbrev const (c : C) : Seq C := .mk (fun _ => c) (fun _ => 𝟙 c)
  abbrev step (s : Seq C) : Seq C := .mk (s.obj ∘ Nat.succ) (fun n => s.map (Nat.succ n))
  abbrev Diagram (C : Type u) [Category.{v, u} C] := Functor ℕ C
  abbrev diagram (s : Seq C) : Seq.Diagram C := Functor.ofSequence s.map

  def byRepeat (f : Functor C C) (z : Σ c : C, c ⟶ f.obj c) : Seq C :=
    let o (n : ℕ) : C := Nat.repeat f.obj n z.1
    let rec m (n : ℕ) : o n ⟶ o (n + 1) := match n with
      | Nat.zero   => z.2
      | Nat.succ n => f.map (m n)
    .mk o m

  lemma step_const (c : C) : (const c).step = const c
    := rfl

  -- TODO: Pointed endofunctor (NatTrans (Functor.id C) f) instead of zm, but what would the naturality give?
  def byRepeat' (f : Functor C C) (m : NatTrans (Functor.id C) f) (z : C) : Seq C :=
    byRepeat f (.mk z (m.app z))

  variable (s : Seq C)

  lemma diagram_map_id {n : ℕ} (o : n ⟶ n) : s.diagram.map o = 𝟙 (s.obj n)
    := by
      rewrite [Subsingleton.elim o (homOfLE (by omega))]
      exact Functor.OfSequence.map_id s.map n

  lemma diagram_map_comp {a b c : ℕ} (o1 : a ⟶ b) (o2 : b ⟶ c) (o3 : a ⟶ c) : s.diagram.map o3 = s.diagram.map o1 ≫ s.diagram.map o2
    := Functor.OfSequence.map_comp s.map a b c (leOfHom o1) (leOfHom o2)

  lemma diagram_map_is_map (n : ℕ) {o : n ⟶ Nat.succ n} : s.diagram.map o = s.map n
    := by
      rewrite [Subsingleton.elim o (homOfLE (Nat.le_add_right n 1))]
      exact Functor.OfSequence.map_le_succ s.map n

  lemma diagram_map_succ_is_comp_map (a b : ℕ) {o1 : a ⟶ b.succ} {o2 : a ⟶ b} : s.diagram.map o1 = s.diagram.map o2 ≫ s.map b
    := by rw [diagram_map_comp s o2 (homOfLE (by omega)) o1 , diagram_map_is_map s b]

  lemma diagram_map_succ_is_step (a b : ℕ) {o1 : a.succ ⟶ b.succ} {o2 : a ⟶ b} : s.diagram.map o1 = s.step.diagram.map o2
    := by rfl

  lemma diagram_map_ext
    (f : {a b : ℕ} → (a ⟶ b) → (s.obj a ⟶ s.obj b))
    (fid : ∀{n : ℕ}{o : n ⟶ n}, f o = 𝟙 (s.obj n))
    (fsucc : ∀{a b : ℕ}{o1 : a ⟶ b}{o2 : a ⟶ b.succ}, f o1 ≫ s.map b = f o2)
    (fstep : ∀{a b : ℕ}{o1 : a ⟶ b}{o2 : a.succ ⟶ b.succ}, (s.diagram.map o1 = f o1) → (s.step.diagram.map o1 = f o2))
    : ∀{a b : ℕ} (o : a ⟶ b), s.diagram.map o = f o
    := by
      simp [const , diagram]
      let rec i a b (o : a ⟶ b) : (Functor.ofSequence s.map).map o = f o := match a , b with
        | 0 , 0 => by simp [diagram_map_id , fid]
        | 0 , Nat.succ b => by
          rewrite [diagram_map_succ_is_comp_map s 0 b (o1 := o) (o2 := homOfLE (by omega))]
          rewrite [i 0 b (homOfLE (by omega))]
          apply fsucc
        | Nat.succ a , Nat.succ b => by
          let o' : a ⟶ b :=
            let _ := leOfHom o
            homOfLE (by omega)
          rewrite [diagram_map_succ_is_step s a b (o1 := o) (o2 := o')]
          exact fstep (i a b o')
      intro a b
      exact i a b

  lemma diagram_map_const (c : C) : ∀{a b : ℕ}(o : a ⟶ b), (Seq.const c).diagram.map o = 𝟙 c
    := diagram_map_ext (Seq.const c) (fun _ => 𝟙 c) rfl (by aesop_cat) (fun p => p)

  lemma diagram_const {c : C} : (Seq.const c).diagram = (Functor.const ℕ).obj c := by
    simp [Functor.ofSequence , Functor.const]
    ext i j o
    exact diagram_map_const c o

  abbrev Mapping (s : Seq C) (d : Seq.Diagram C) := NatTrans s.diagram d
  namespace Mapping
    variable {s : Seq C}
    variable {d : Seq.Diagram C}
    variable {t : Seq.Mapping s d}

    def mk
      (p : (n : ℕ) → s.obj n ⟶ d.obj n)
      (eq : ∀(n : ℕ)(o : n ⟶ n.succ), s.map n ≫ p (Nat.succ n) = p n ≫ d.map o)
      : Seq.Mapping s d :=
        NatTrans.ofSequence (F := s.diagram) (G := d) p (by
          intro n
          rewrite [s.diagram_map_is_map n]
          exact eq n _
        )

  end Mapping

  abbrev Morphism (s1 s2 : Seq C) := NatTrans s1.diagram s2.diagram
  namespace Morphism
    variable {s s1 s2 : Seq C}
    variable {t : Seq.Morphism s1 s2}

    def mk
      (p : (n : ℕ) → s1.obj n ⟶ s2.obj n)
      (eq : ∀(n : ℕ), s1.map n ≫ p (Nat.succ n) = p n ≫ s2.map n)
      : Seq.Morphism s1 s2 := Mapping.mk p (by simp [s2.diagram_map_is_map , eq])

    @[reassoc]
    theorem condition (n : ℕ) : s1.map n ≫ t.app (Nat.succ n) = t.app n ≫ s2.map n
      := by
        let o : n ⟶ Nat.succ n := homOfLE (by omega)
        rewrite [(s1.diagram_map_is_map n (o := o)).symm]
        rewrite [(s2.diagram_map_is_map n (o := o)).symm]
        exact t.naturality o

    def step (t : Seq.Morphism s1 s2) : Seq.Morphism s1.step s2.step
      := Morphism.mk
        (fun n => t.app n.succ)
        (fun n => condition n.succ (t := t))

  end Morphism

  instance category : Category (Seq C) where
    Hom := Seq.Morphism
    id s := NatTrans.id s.diagram
    comp := NatTrans.vcomp

end Seq

abbrev HasSeqColimit(s : Seq C) := HasColimit s.diagram
noncomputable abbrev seqColim (s : Seq C) [HasSeqColimit s] := colimit s.diagram

noncomputable abbrev seqColim.ι (s : Seq C) [HasSeqColimit s] (n : ℕ)
  : s.obj n ⟶ seqColim s
  := colimit.ι s.diagram n






variable (s : Seq C)
variable {W : C}
variable {p : (n : ℕ) → s.obj n ⟶ W}
variable {eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n}

-- Follows the structure of https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.html
abbrev SeqColimCocone := Cocone s.diagram
namespace SeqColimCocone
  variable {s : Seq C}
  variable {t : SeqColimCocone s}

  -- It could be using Seq.Morphism.mk, but it is not.
  def mk
    (p : (n : ℕ) → s.obj n ⟶ W) -- TODO: Is it really enough when W is not dependent on n?
    (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
    : SeqColimCocone s where
    pt := W
    ι := Seq.Mapping.mk p (by simp [eq])

  abbrev ι (t : SeqColimCocone s) (n : ℕ) : s.obj n ⟶ t.pt
    := (Cocone.ι t).app n

  @[reassoc]
  theorem condition (n : ℕ)
    : s.map n ≫ ι t (Nat.succ n) = ι t n
    := by
      let o : n ⟶ Nat.succ n := homOfLE (by omega)
      rewrite [(s.diagram_map_is_map n (o := o)).symm]
      exact Cocone.w t o

  def step (t : SeqColimCocone s)
    : SeqColimCocone s.step
    := SeqColimCocone.mk
      (fun n => ι t (Nat.succ n))
      (fun n => condition (Nat.succ n) (t := t))

  def unstep (t : SeqColimCocone s.step)
    : SeqColimCocone s
    := SeqColimCocone.mk
      (fun n => s.map n ≫ ι t n)
      (fun n => congr_arg _ (condition n (t := t)))

  def stepIsColimit (ht : IsColimit t) : IsColimit t.step
    := IsColimit.mk
      (fun s => ht.desc (unstep s))
      (fun t' n => by
        simp [Seq.Mapping.mk , step , mk , unstep , ι]
        exact condition n (t := t')
      )
      (fun t' f e => by
        simp [Seq.Mapping.mk , mk , unstep , ι]
        apply IsColimit.hom_ext ht
        intro n
        simp
        rewrite [(e n).symm]
        simp [Seq.Mapping.mk , step , mk , ι]
        simp [condition_assoc n (t := t) f]
      )

end SeqColimCocone

noncomputable abbrev seqColim.cocone
  [HasSeqColimit s]
  := colimit.cocone s.diagram

noncomputable abbrev seqColim.desc
  [HasSeqColimit s]
  (p : (n : ℕ) → s.obj n ⟶ W)
  (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
  : seqColim s ⟶ W
  := colimit.desc s.diagram (SeqColimCocone.mk p eq)

@[reassoc]
theorem seqColim.ι_desc
  [HasSeqColimit s]
  (p : (n : ℕ) → s.obj n ⟶ W)
  (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
  (n : ℕ)
  : seqColim.ι _ n ≫ seqColim.desc s p eq = p n
  := colimit.ι_desc _ _

@[reassoc]
theorem seqColim.condition
  [HasSeqColimit s]
  (n : ℕ)
  : s.map n ≫ seqColim.ι s (Nat.succ n) = seqColim.ι s n
  := SeqColimCocone.condition n

-- def seqColimIsSeqColim
--   [HasSeqColimit s.diagram]
--   : IsColimit (SeqColimCocone.mk (seqColim.ι) seqColim.condition)
--   := SeqColimCocone.IsColimit.mk _ (fun s => seqColim.desc s.ι s.condition) (by simp) (by simp) (by aesop_cat)
--
-- instance hasSeqColimit_step [HasSeqColimit s.diagram]
--   : HasSeqColimit (s.diagram.step) -- TODO: Where is the dependent function composition?
--   := ⟨⟨⟨_, SeqColimCocone.stepIsColimit (seqColimIsSeqColim s)⟩⟩⟩
--
-- def seqColim_step
--   [HasSeqColimit s.diagram]
--   : seqColim s.diagram ≅ seqColim (s.diagram.step)
--   := IsColimit.coconePointUniqueUpToIso (SeqColimCocone.stepIsColimit (seqColimIsSeqColim s)) (colimit.isColimit _)

end Limits
