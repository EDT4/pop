import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Data.Nat.EvenOddRec
import Pop.NatExtras

-- Source: Sequential Colimits in Homotopy Type Theory [https://who.rocq.inria.fr/Kristina.Sojakova/papers/sequential_colimits_homotopy.pdf]
-- Follows the structure of https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.html
namespace CategoryTheory.Limits

open CategoryTheory
open CategoryTheory.Limits

variable {C C₁ C₂ : Type _}
variable [Category C]
variable [Category C₁]
variable [Category C₂]

-- 3.1
-- An equivalent form:
--   First some definitions:
--
--     def SuccQuiver := ℕ
--     inductive Succ : SuccQuiver → SuccQuiver → Prop where
--     | succ : (n : ℕ) → Succ n n.succ
--     instance SuccQuiverQuiver : Quiver SuccQuiver where Hom := Succ
--
--   Then Seq is equivalent to Seq' witnessed by the following:
--
--     def Seq' := Prefunctor SuccQuiver
--     def Seq'.map (s : Seq' C) n := Prefunctor.map s (Succ.succ n)
--     def mk.map (s : Seq C) : ∀{X Y}, Succ X Y → (s.obj X ⟶ s.obj Y)
--     | n , _ , Succ.succ n => s.map n
--     def mk (s : Seq C) : Seq' C where
--       obj := s.obj
--       map := mk.map s
--
--   and the diagram would be given by "Mathlib.Combinatorics.Quiver.Path".
structure Seq (C : Type _) [Quiver C] where
  obj : ℕ → C
  map : (n : ℕ) → obj n ⟶ obj (Nat.succ n)
namespace Seq
  abbrev const (c : C) : Seq C := .mk (fun _ => c) (fun _ => 𝟙 c)
  abbrev step (s : Seq C) : Seq C := .mk (s.obj ∘ Nat.succ) (fun n => s.map (Nat.succ n))
  abbrev add (k : ℕ) (s : Seq C) : Seq C := Nat.iterate step k s
  abbrev prepend (s : Seq C) (e : Over (s.obj 0)) : Seq C where
    obj n := Nat.casesAuxOn n e.left s.obj
    map n := Nat.casesAuxOn n e.hom  s.map

  abbrev Diagram (C : Type _) [Category C] := Functor ℕ C
  abbrev diagram (s : Seq C) : Seq.Diagram C := Functor.ofSequence s.map
  abbrev Diagram.seq (d : Seq.Diagram C) : Seq C := .mk d.obj (fun _ => d.map (homOfLE (by omega)))

  lemma step_const (c : C) : (const c).step = const c := rfl

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

  lemma seq_map_is_map {d : Seq.Diagram C} {n : ℕ} {o : n ⟶ n.succ} : (Diagram.seq d).map n = d.map o := rfl

  -- 3.4
  @[ext]
  structure Hom (s₁ s₂ : Seq C) where
    obj : (n : ℕ) → s₁.obj n ⟶ s₂.obj n
    map : ∀(n : ℕ), s₁.map n ≫ obj (Nat.succ n) = obj n ≫ s₂.map n := by aesop_cat

  attribute [reassoc (attr := simp)] Hom.map

  namespace Hom
    variable {s s₁ s₂ s₃ : Seq C}
    variable {t : Hom s₁ s₂}

    def diagram_hom (t : Hom s₁ s₂)
      : NatTrans s₁.diagram s₂.diagram
      := NatTrans.ofSequence (F := s₁.diagram) (G := s₂.diagram) t.obj (by
        intro n
        rewrite [s₁.diagram_map_is_map n]
        rewrite [s₂.diagram_map_is_map n]
        exact t.map _
      )

    @[reassoc]
    def diagram_hom_condition {t : NatTrans s₁.diagram s₂.diagram} (n : ℕ)
      : s₁.map n ≫ t.app (Nat.succ n) = t.app n ≫ s₂.map n
      := by
        let o : n ⟶ Nat.succ n := homOfLE (by omega)
        rewrite [← s₁.diagram_map_is_map n (o := o)]
        rewrite [← s₂.diagram_map_is_map n (o := o)]
        exact t.naturality o

    def seq {f g : Diagram C} (t : NatTrans f g) : Hom f.seq g.seq where
      obj   := t.app
      map _ := t.naturality (homOfLE (by omega))

    def step (t : Hom s₁ s₂) : Hom s₁.step s₂.step
      := .mk (fun n => t.obj n.succ) (fun n => t.map n.succ)

    abbrev comp (t₁ : Seq.Hom s₁ s₂) (t₂ : Seq.Hom s₂ s₃) : Seq.Hom s₁ s₃ where
      obj n := t₁.obj n ≫ t₂.obj n

  end Hom

  @[simps]
  instance category : Category (Seq C) where
    Hom := Hom
    id s := .mk (fun n => 𝟙 (s.obj n))
    comp := Hom.comp

  def repeats (f : Functor C C) (z : Σ c : C, c ⟶ f.obj c) : Seq C where
    obj n := Nat.repeat f.obj n z.1
    map   := Nat.rec z.2 (fun _ => f.map)

  def iterate {C : Type _} [Bicategory C] {c : C} (f : c ⟶ c) (m : 𝟙 c ⟶ f) : Seq (c ⟶ c) where
    obj := Nat.rec (𝟙 c) (fun _ r => r ≫ f)
    map := Nat.rec (m ≫ (Bicategory.leftUnitor f).symm.hom) (fun _ r => Bicategory.whiskerRight r f)

  -- def iterate2 (f g : Functor C C) (mf : NatTrans (𝟭 C) f) (mg : NatTrans (𝟭 C) g) : Seq (Functor C C) :=
  --   let obj : ℕ → C ⥤ C := Nat.rec2 (𝟭 C) (fun _ r => r ⋙ f) (fun _ r => r ⋙ g)
  --   let map : (n : ℕ) → obj n ⟶ obj n.succ := Nat.rec2 mf
  --     (fun {n} e _ => by
  --       simp [obj]
  --       rewrite [Nat.rec2_odd_step (Nat.even_add_one'.mpr e) , Nat.rec2_even_step e]
  --       exact whiskerLeft (obj n) (whiskerLeft f mg)
  --     )
  --     (fun {n} e _ => by
  --       simp [obj]
  --       rewrite [Nat.rec2_even_step (Nat.even_add_one.mpr e) , Nat.rec2_odd_step e]
  --       exact whiskerLeft (obj n) (whiskerLeft g mf)
  --     )
  --   {obj := obj , map := map}

  def iterate2 {C : Type _} [Bicategory C] {c : C} (f g : c ⟶ c) (mf : 𝟙 c ⟶ f) (mg : 𝟙 c ⟶ g) : Seq (c ⟶ c) :=
    let obj : ℕ → (c ⟶ c) := Nat.rec2 (𝟙 c) (fun _ r => r ≫ f) (fun _ r => r ≫ g)
    let map : (n : ℕ) → obj n ⟶ obj n.succ := Nat.rec2 (mf ≫ (Bicategory.leftUnitor f).symm.hom)
      (fun {n} e _ => by
        simp [obj]
        rewrite [Nat.rec2_odd_step (Nat.even_add_one'.mpr e) , Nat.rec2_even_step e]
        exact Bicategory.whiskerLeft (obj n) ((Bicategory.rightUnitor f).symm.hom ≫ Bicategory.whiskerLeft f mg) ≫ (Bicategory.associator (obj n) f g).symm.hom
      )
      (fun {n} e _ => by
        simp [obj]
        rewrite [Nat.rec2_even_step (Nat.even_add_one.mpr e) , Nat.rec2_odd_step e]
        exact Bicategory.whiskerLeft (obj n) ((Bicategory.rightUnitor g).symm.hom ≫ Bicategory.whiskerLeft g mf) ≫ (Bicategory.associator (obj n) g f).symm.hom
      )
    {obj := obj , map := map}

  def iterate2_property
    {C : Type _} [Bicategory C] {c : C} {f g : c ⟶ c} {mf : 𝟙 c ⟶ f} {mg : 𝟙 c ⟶ g}
    (P : (n : ℕ) → (c ⟶ c) → Sort _)
    (p0 : P 0 (𝟙 c))
    (ps0 : {n : ℕ} →  Even n → {a : c ⟶ c} → P n a → P n.succ (a ≫ f))
    (ps1 : {n : ℕ} → ¬Even n → {a : c ⟶ c} → P n a → P n.succ (a ≫ g))
    {n : ℕ}
    : P n ((iterate2 f g mf mg).obj n)
    := Nat.rec2_property (fun {n} => P n) p0 (fun {_}{e} => ps0 e) (fun {_}{e} => ps1 e) n

  def iterate2_even_property
    {C : Type _} [Bicategory C] {c : C} {f g : c ⟶ c} {mf : 𝟙 c ⟶ f} {mg : 𝟙 c ⟶ g}
    (P : {n : ℕ} → Even n → (c ⟶ c) → Sort _)
    (p0 : P Even.zero (𝟙 c))
    (ps : {n : ℕ} → {e : Even n} → {a : c ⟶ c} → P e a → P (Nat.even_add_two.mpr e) ((a ≫ f) ≫ g))
    : {n : ℕ} → (e : Even n) → P e ((iterate2 f g mf mg).obj n)
    := Nat.rec2_even_property P p0 ps

  def iterate2_odd_property
    {C : Type _} [Bicategory C] {c : C} {f g : c ⟶ c} {mf : 𝟙 c ⟶ f} {mg : 𝟙 c ⟶ g}
    (P : {n : ℕ} → ¬Even n → (c ⟶ c) → Sort _)
    (p1 : P (Nat.even_add_one'.mpr Even.zero) (𝟙 c ≫ f))
    (ps : {n : ℕ} → {e : ¬Even n} → {a : c ⟶ c} → P e a → P (Nat.even_add_two.not.mpr e) ((a ≫ g) ≫ f))
    : {n : ℕ} → (e : ¬Even n) → P e ((iterate2 f g mf mg).obj n)
    := Nat.rec2_odd_property P p1 ps

end Seq

abbrev HasSeqColimit(s : Seq C) := HasColimit s.diagram
abbrev HasSeqColimits(C : Type _) [Category C] := HasColimitsOfShape ℕ C

-- 3.2
noncomputable abbrev seqColim (s : Seq C) [HasSeqColimit s] := colimit s.diagram

noncomputable abbrev seqColim.ι (s : Seq C) [HasSeqColimit s] (n : ℕ)
  : s.obj n ⟶ seqColim s
  := colimit.ι s.diagram n

variable (s s₁ s₂ s₃ : Seq C)
variable [HasSeqColimit s]
variable [HasSeqColimit s₁]
variable [HasSeqColimit s₂]
variable [HasSeqColimit s₃]
variable {W : C}

-- Follows the structure of https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.html
abbrev SeqColimCocone := Cocone s.diagram
namespace SeqColimCocone
  variable {s : Seq C}
  variable {t : SeqColimCocone s}
  -- variable {p : (n : ℕ) → s.obj n ⟶ W}
  -- variable {eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n}

  def mk
    (p : (n : ℕ) → s.obj n ⟶ W)
    (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
    : SeqColimCocone s where
    pt := W
    ι := NatTrans.ofSequence (F := s.diagram) (G := (Functor.const ℕ).obj W) p (by simp [s.diagram_map_is_map,eq])

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
      (by
        intro t' n
        simp [step , mk , unstep , ι]
        exact condition n (t := t')
      )
      (by
        intro t' f e
        simp [mk , unstep , ι]
        apply IsColimit.hom_ext ht
        intro n
        simp
        rewrite [(e n).symm]
        simp [step , mk , ι]
        simp [condition_assoc n (t := t) f]
      )

  def unstepIsColimit {t : SeqColimCocone s.step} (ht : IsColimit t) : IsColimit t.unstep
    := IsColimit.mk
      (fun s => ht.desc (step s))
      (by
        intro t' n
        simp [step , mk , unstep , ι]
        exact condition n (t := t')
      )
      (by
        intro t' f e
        simp [mk , step , ι]
        apply IsColimit.hom_ext ht
        intro n
        simp
        rewrite [(e n.succ).symm]
        simp [unstep , mk , ι]
        simp [condition_assoc n (t := t) f]
      )

end SeqColimCocone

variable {s s₁ s₂ s₃}
variable (t t₁ : s₁ ⟶ s₂)
variable (t₂ : s₂ ⟶ s₃)

noncomputable abbrev seqColim.cocone
  := colimit.cocone s.diagram

noncomputable abbrev seqColim.desc
  [HasSeqColimit s]
  (p : (n : ℕ) → s.obj n ⟶ W)
  (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
  : seqColim s ⟶ W
  := colimit.desc s.diagram (SeqColimCocone.mk p eq)

@[reassoc]
theorem seqColim.ι_desc
  (p : (n : ℕ) → s.obj n ⟶ W)
  (eq : ∀(n : ℕ), s.map n ≫ p (Nat.succ n) = p n)
  (n : ℕ)
  : seqColim.ι _ n ≫ seqColim.desc p eq = p n
  := colimit.ι_desc _ _

@[reassoc]
theorem seqColim.condition
  (n : ℕ)
  : s.map n ≫ seqColim.ι s (Nat.succ n) = seqColim.ι s n
  := SeqColimCocone.condition n

-- 3.3
@[ext 1100]
theorem seqColim.hom_ext
  {f g : seqColim s ⟶ W}
  : (∀(n : ℕ), seqColim.ι s n ≫ f = seqColim.ι s n ≫ g) → (f = g)
  := colimit.hom_ext

noncomputable def seqColimIsSeqColim : IsColimit (SeqColimCocone.mk (seqColim.ι s) seqColim.condition)
  := IsColimit.mk
    (fun t => seqColim.desc (SeqColimCocone.ι t) SeqColimCocone.condition)
    (by simp [SeqColimCocone.mk])
    (by simp [SeqColimCocone.mk] ; aesop_cat)

instance hasSeqColimit_step : HasSeqColimit (s.step)
  := ⟨_ , SeqColimCocone.stepIsColimit seqColimIsSeqColim⟩

-- 3.6
noncomputable def seqColim_step : seqColim s ≅ seqColim (s.step)
  := IsColimit.coconePointUniqueUpToIso (SeqColimCocone.stepIsColimit seqColimIsSeqColim) (colimit.isColimit _)

-- 3.5.1
noncomputable abbrev seqColim.map
  (t : Seq.Hom s₁ s₂)
  : seqColim s₁ ⟶ seqColim s₂
  := seqColim.desc
    (fun n => t.obj n ≫ seqColim.ι s₂ n)
    (by intro ; simp ; rw [condition])

-- 3.5.2
@[simp]
lemma seqColim.map_id
  : seqColim.map (𝟙 s) = 𝟙 (seqColim s)
  := by ext ; simp [SeqColimCocone.mk]

-- 3.5.3
@[reassoc]
lemma seqColim.map_comp : seqColim.map t₁ ≫ seqColim.map t₂ = seqColim.map (t₁ ≫ t₂)
  := by ext ; simp [SeqColimCocone.mk]

-- 3.5.4
lemma seqColim.map_ext
  {t₁ t₂ : s₁ ⟶ s₂}
  (h : ∀{n}, t₁.obj n = t₂.obj n)
  : seqColim.map t₁ = seqColim.map t₂
  := by
    simp [seqColim.map,desc]
    congr
    ext
    rw [h]

noncomputable def seqColim.congrHom
  (t : s₁ ≅ s₂)
  : seqColim s₁ ≅ seqColim s₂
  where
    hom := seqColim.map t.hom
    inv := seqColim.map t.inv
    hom_inv_id := by rw [map_comp,t.hom_inv_id,map_id]
    inv_hom_id := by rw [map_comp,t.inv_hom_id,map_id]

-- 3.5.5
instance seqColim.map_isIso [IsIso t] : IsIso (seqColim.map t)
  := ⟨seqColim.map (inv t) , by constructor <;> (rw [map_comp] ; aesop_cat)⟩

-- def iterate_comp
--   {f g : Functor C C}{m₁ : NatTrans (𝟭 C) (f ⋙ g)}{m₂ : NatTrans (𝟭 C) (g ⋙ f)} [HasSeqColimits (Functor C C)]
--   : seqColim (Seq.iterate (f ⋙ g) m₁) ≅ seqColim (Seq.iterate (g ⋙ f) m₂)
--   := sorry
