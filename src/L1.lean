import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where
import tactic.omega

namespace L1
  -- State
  def State := string → int
  def State.update (name : string) (val : int) (s : State) : State :=
    λname', if name' = name then val else s name'
  instance : has_emptyc State := { emptyc := λ_, 0 }
  
  inductive Oper : Type
    | Plus : Oper
    | Gteq : Oper

  inductive Expr : Type
    | Integer : int → Expr
    | Deref : string → Expr
    | Op : Expr → Oper → Expr → Expr
    | Boolean : bool → Expr
    | Skip : Expr
    | Assign : string → Expr → Expr
    | Seq : Expr → Expr → Expr
    | If : Expr → Expr → Expr → Expr
    | While : Expr → Expr → Expr
  
  notation s `{` name ` ↦ ` val `}` := State.update name val s

  notation `!`l := Expr.Deref l
  notation a1 ` PLUS `:60 a2 := Expr.Op a1 Oper.Plus a2
  notation `I`:10000000 n := Expr.Integer n
  notation `B`:10000000 b := Expr.Boolean b

  notation a1 ` GTEQ`:60 a2 := Expr.Op a1 Oper.Gteq a2
  
  notation l ` :== `:51 e := Expr.Assign l e
  notation `IF ` b ` THEN ` c1 ` ELSE` c2 := Expr.If b c1 c2
  notation `WHILE ` b ` DO ` c := Expr.While b c
  notation `SKIP` := Expr.Skip
  notation c1 `;`:100 c2 := Expr.Seq c1 c2

  notation `⟨` a `,` b `⟩` := (a, b)

  #check (
    SKIP;
    "a" :== (I 1);
    "b" :== (I 2) PLUS (I 3);
    IF (!"b" GTEQ (I 1)) THEN (
      "b" :== !"b" PLUS (I 1)
    ) ELSE (
      SKIP
    );
    WHILE (!"b" GTEQ (I 1)) DO (
      "b" :== !"b" PLUS (I 1)
    )
  )

  inductive small_step : Expr × State → Expr × State → Prop 
    | op_plus (n₁ n₂ s) : 
      small_step ⟨(I n₁) PLUS (I n₂), s⟩ ⟨I (n₁ + n₂), s⟩
    | op_gteq (n₁ n₂ s) : 
      small_step ⟨(I n₁) GTEQ (I n₂), s⟩ ⟨(B (n₁ ≥ n₂)), s⟩
    
    | op1 (e₁ e₁' e₂ s s' op) (h : small_step ⟨e₁, s⟩ ⟨e₁', s'⟩) : 
      small_step ⟨Expr.Op e₁ op e₂, s⟩ ⟨Expr.Op e₁' op e₂, s'⟩
    | op2_i (n e₂ e₂' s s' op) (h : small_step ⟨e₂, s⟩ ⟨e₂', s'⟩) : 
      small_step ⟨Expr.Op (I n) op e₂, s⟩ ⟨Expr.Op (I n) op e₂', s'⟩
    | op2_b (b e₂ e₂' s s' op) (h : small_step ⟨e₂, s⟩ ⟨e₂', s'⟩) : 
      small_step ⟨Expr.Op (B b) op e₂, s⟩ ⟨Expr.Op (B b) op e₂', s'⟩
    | op2_s (e₂ e₂' s s' op) (h : small_step ⟨e₂, s⟩ ⟨e₂', s'⟩) : 
      small_step ⟨Expr.Op SKIP op e₂, s⟩ ⟨Expr.Op SKIP op e₂', s'⟩
    
    | deref (l s) : 
      small_step ⟨!l, s⟩ ⟨I (s l), s⟩
    | assign1 (l n s) : 
      small_step ⟨l :== (I n), s⟩ ⟨SKIP, s {l ↦ n}⟩
    | assign2 (e e' l s s') (h : small_step ⟨e, s⟩ ⟨e', s'⟩) : 
      small_step ⟨l :== e, s⟩ ⟨l :== e', s'⟩
    
    | seq1 (e₂: Expr) (s: State) :
      small_step ⟨SKIP; e₂, s⟩ ⟨e₂, s⟩
    | seq2 (e₁ e₁' e₂ : Expr) (s s') (h : small_step ⟨e₁, s⟩ ⟨e₁', s'⟩) :
      small_step ⟨e₁; e₂, s⟩ ⟨e₁'; e₂, s'⟩
    
    | if1 (e₂ e₃: Expr) (s: State) :
      small_step ⟨IF (B true) THEN e₂ ELSE e₃, s⟩ ⟨e₂, s⟩
    | if2 (e₂ e₃: Expr) (s: State) :
      small_step ⟨IF (B false) THEN e₂ ELSE e₃, s⟩ ⟨e₃, s⟩
    | if3 (e₁ e₁' e₂ e₃: Expr) (s s': State) :
      small_step ⟨IF e₁ THEN e₂ ELSE e₃, s⟩ ⟨IF e₁' THEN e₂ ELSE e₃, s⟩
    
    | while (e₁ e₂: Expr) (s: State) :
      small_step ⟨WHILE e₁ DO e₂, s⟩ ⟨IF e₁ THEN (e₂; WHILE e₁ DO e₂) ELSE SKIP, s⟩

  notation a ` ⟶ ` b  := small_step a b

  #check ⟨(I 2) PLUS (I 3), ∅⟩ ⟶ ⟨(I 2) PLUS (I 3), ∅⟩
  
  -- # Interpreter (TODO)
  def run : ℕ × State × Expr → option (ℕ × State × Expr)
    | (0, _, _) := option.none
    | (gas, s, I a) := option.none
    | (gas, s, B b) := option.none
    | (gas, s, Expr.Op e₁ op e₂) := (
      match e₁, op, e₂ with
      | (I n₁), Oper.Plus, (I n₂) := option.some (gas-1, s, I (n₁ + n₂))
      | (I n₁), Oper.Gteq, (I n₂) := option.some (gas-1, s, B (n₁ ≥ n₂))
      | (I n₁), op, e₂ := sorry
      | e₁, op, e₂ := sorry
      end
    )
    | (gas, s, !x) := sorry
    | (gas, s, SKIP) := sorry
    | (gas, s, l :== (I n)) := sorry
    | (gas, s, e₁; e₂) := sorry
    | (gas, s, IF b THEN e₂ ELSE e₃) := sorry
    | (gas, s, WHILE e₁ DO e₂) := sorry
    | _ := option.none

end L1