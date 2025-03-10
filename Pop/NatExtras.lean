import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity

def Nat.even_add_two
  {n : ℕ}
  : Even (n + 2) ↔ Even n
  := (Nat.even_add (n := 2)).trans (.intro (fun p => p.mpr even_two) (fun p => .intro (fun _ => even_two) (fun _ => p)))

theorem Nat.even_add_one' {n : ℕ} : ¬Even n.succ ↔ Even n
  := Nat.even_add_one.symm.trans Nat.even_add_two

def Nat.rec2r
  {A : ℕ → Sort _}
  (zero : A 0)
  (succ0 : {n : ℕ} → A n → A n.succ)
  (succ1 : {n : ℕ} → A n → A n.succ)
  : (n : Nat) → A n
  | Nat.zero   => zero
  | Nat.succ n => succ0 (Nat.rec2r zero succ1 succ0 n)

def Nat.rec2r_even_property
  {A : ℕ → Sort _}
  {zero : A 0}
  {succ0 : {n : ℕ} → A n → A n.succ}
  {succ1 : {n : ℕ} → A n → A n.succ}
  (P : {n : ℕ} → Even n → A n → Sort _)
  (p0 : P Even.zero zero)
  (ps : {n : ℕ} → {e : Even n} → {a : A n} → P e a → P (Nat.even_add_two.mpr e) (succ0 (succ1 a)))
  : {n : ℕ} → (e : Even n) → P e (Nat.rec2r zero succ0 succ1 n)
  | 0     , _ => p0
  | 1     , e => by absurd e ; decide
  | n + 2 , e => ps (Nat.rec2r_even_property P p0 ps (Nat.even_add_two.mp e))

def Nat.rec2r_odd_property
  {A : ℕ → Sort _}
  {zero : A 0}
  {succ0 : {n : ℕ} → A n → A n.succ}
  {succ1 : {n : ℕ} → A n → A n.succ}
  (P : {n : ℕ} → ¬Even n → A n → Sort _)
  (p1 : P (Nat.even_add_one'.mpr Even.zero) (succ0 zero))
  (ps : {n : ℕ} → {e : ¬Even n} → {a : A n} → P e a → P (Nat.even_add_two.not.mpr e) (succ0 (succ1 a)))
  : {n : ℕ} → (e : ¬Even n) → P e (Nat.rec2r zero succ0 succ1 n)
  | 0     , e => by absurd e ; decide
  | 1     , _ => p1
  | n + 2 , e => ps (Nat.rec2r_odd_property P p1 ps (Nat.even_add_two.not.mp e))

def Nat.rec2l
  {A : ℕ → Sort _}
  (zero : A 0)
  (succ0 : {n : ℕ} →  Even n → A n → A n.succ)
  (succ1 : {n : ℕ} → ¬Even n → A n → A n.succ)
  : (n : Nat) → A n
  | 0     => zero
  | n + 1 => Nat.rec2l
    (A := fun n => A n.succ)
    (succ0 Even.zero zero)
    (fun e => succ1 (Nat.even_add_one'.mpr e))
    (fun e => succ0 (Nat.even_add_one.mpr e))
    n

lemma Nat.rec2l_even_step
  {A : ℕ → Sort _}
  {zero : A 0}
  {succ0 : {n : ℕ} →  Even n → A n → A n.succ}
  {succ1 : {n : ℕ} → ¬Even n → A n → A n.succ}
  {n : ℕ} (p : Even n)
  : Nat.rec2l zero succ0 succ1 n.succ = succ0 p (Nat.rec2l zero succ0 succ1 n)
  := match n with
  | 0     => rfl
  | 1     => by absurd p ; decide
  | n + 2 => Nat.rec2l_even_step
    (A := fun n => A n.succ.succ)
    (zero := succ1 (by decide) (succ0 Even.zero zero))
    (succ0 := fun e => succ0 (Nat.even_add_two.mpr e))
    (succ1 := fun e => succ1 (Nat.even_add_two.not.mpr e))
    (n := n)
    (Nat.even_add_two.mp p)
  -- Nat.rec2_even_property
  --   (fun {n} p a => Nat.rec2 zero succ0 succ1 n.succ = succ0 p a)
  --   rfl
  --   sorry

lemma Nat.rec2l_odd_step
  {A : ℕ → Sort _}
  {zero : A 0}
  {succ0 : {n : ℕ} →  Even n → A n → A n.succ}
  {succ1 : {n : ℕ} → ¬Even n → A n → A n.succ}
  {n : ℕ} (p :  ¬Even n)
  : Nat.rec2l zero succ0 succ1 n.succ = succ1 p (Nat.rec2l zero succ0 succ1 n)
  := match n with
  | 0     => by absurd p ; decide
  | 1     => rfl
  | n + 2 => Nat.rec2l_odd_step
    (A := fun n => A n.succ.succ)
    (zero := succ1 (by decide) (succ0 Even.zero zero))
    (succ0 := fun e => succ0 (Nat.even_add_two.mpr e))
    (succ1 := fun e => succ1 (Nat.even_add_two.not.mpr e))
    (n := n)
    (Nat.even_add_two.not.mp p)


mutual
  variable {A : ℕ → Sort _}
  variable (zero : A 0)
  variable (succ0 : {n : ℕ} →  Even n → A n → A n.succ)
  variable (succ1 : {n : ℕ} → ¬Even n → A n → A n.succ)

  def Nat.rec2'_even : (n : Nat) → Even n → A n
    | 0   , _ => zero
    | n+1 , e =>
      let e' := Nat.even_add_one.mp e
      succ1 e' (Nat.rec2'_odd n e')

  def Nat.rec2'_odd : (n : Nat) → ¬Even n → A n
    | n+1 , e =>
      let e' := Nat.even_add_one'.mp e
      succ0 e' (Nat.rec2'_even n e')

  def Nat.rec2' (n : Nat) : A n := Decidable.casesOn (Nat.instDecidablePredEven n) (Nat.rec2'_odd n) (Nat.rec2'_even n)
end
