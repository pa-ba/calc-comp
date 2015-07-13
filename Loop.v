(** Calculation of a compiler for an imperative language with
unbounded loops. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Get : Expr.

Inductive Stmt : Set :=
| Put : Expr -> Stmt
| Seqn : Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt.

(** * Semantics *)

Definition State := nat.
Reserved Notation "x ⇓[ q ] y" (at level 80, no associativity).

Inductive eval : Expr -> State -> nat -> Prop :=
| eval_val q n : Val n ⇓[q] n
| eval_add q x y m n : x ⇓[q] m -> y ⇓[q] n -> Add x y ⇓[q] (m + n)
| eval_get q : Get ⇓[q] q
where "x ⇓[ q ] y" := (eval x q y).

Reserved Notation "x ↓[ q ] q'" (at level 80, no associativity).

Inductive run : Stmt -> State -> State -> Prop :=
| run_put x q v : x ⇓[q] v -> Put x ↓[q] v
| run_seqn x1 x2 q1 q2 q3 : x1 ↓[q1] q2 -> x2 ↓[q2] q3 -> Seqn x1 x2 ↓[q1] q3
| run_while_exit x1 x2 q : x1 ⇓[q] 0 -> While x1 x2 ↓[q] q
| run_while_cont v x1 x2 q1 q2 q3 : x1 ⇓[q1] v -> v > 0 -> x2 ↓[q1] q2 -> While x1 x2 ↓[q2] q3 
                   -> While x1 x2 ↓[q1] q3
where "x ↓[ q ] y" := (run x q y).

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| GET : Code -> Code
| PUT : Code -> Code
| LOOP : Code
| JMP : Code -> Code -> Code
| ENTER : Code -> Code
| HALT : Code.

Fixpoint compE (x : Expr) (c : Code) : Code :=
  match x with
    | Val n => PUSH n c
    | Add x1 x2 => compE x1 (compE x2 (ADD c))
    | Get => GET c
  end.

Fixpoint compS (x : Stmt) (c : Code) : Code :=
  match x with
    | Put x => compE x (PUT c)
    | Seqn x1 x2 => compS x1 (compS x2 c)
    | While x1 x2 => ENTER (compE x1 (JMP c (compS x2 LOOP)))
  end.

Definition comp (x : Stmt) : Code := compS x HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| CON : Code -> Elem
.

Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> State -> Conf.

Notation "⟨ c , s , q ⟩" := (conf c s q).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c q s :  ⟨PUSH n c, s, q⟩ ==> ⟨c, VAL n :: s, q⟩ 
| vm_add c m n q s : ⟨ADD c, VAL n :: VAL m :: s, q⟩ 
                        ==> ⟨c, VAL (m + n) :: s, q⟩
| vm_get c q s : ⟨GET c, s, q⟩ ==> ⟨c, VAL q :: s, q⟩
| vm_put c v s q : ⟨PUT c, VAL v :: s, q⟩ ==> ⟨c, s, v⟩
| vm_loop c s q : ⟨LOOP, CON c :: s, q⟩ ==> ⟨c, s, q⟩
| vm_jmp_yes v c c' s q : v > 0 -> ⟨JMP c' c, VAL v :: s, q⟩ ==> ⟨c, s, q⟩
| vm_jmp_no  c c' c'' s q : ⟨JMP c' c, VAL 0 :: CON c'' :: s, q⟩ ==> ⟨c', s, q⟩
| vm_enter c s q : ⟨ENTER c, s, q⟩ ==> ⟨c, CON (ENTER c) :: s, q⟩
where "x ==> y" := (VM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler for expressions *)
Theorem specExpr x q v s c : x ⇓[q] v -> ⟨compE x c, s, q⟩ 
                                 =>> ⟨c , VAL v :: s, q⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.

(** Calculation of the compiler for expressions *)

(** - [Val n ⇓[q] n]: *)

  begin
  ⟨c, VAL n :: s, q⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, q⟩.
  [].

(** - [Add x y ⇓[q] (m + n)]: *)

  begin
    ⟨c, VAL (m + n) :: s, q ⟩.
  <== { apply vm_add }
    ⟨ADD c, VAL n :: VAL m :: s, q⟩. 
  <<= { apply IHeval2 }
  ⟨compE y (ADD c), VAL m :: s, q⟩.
  <<= { apply IHeval1 }
  ⟨compE x (compE y (ADD c)), s, q⟩.
  [].

(** - [Get ⇓[q] q]: *)

  begin
    ⟨c, VAL q :: s, q⟩.
  <== {apply vm_get}
    ⟨GET c, s, q ⟩.
   [].
Qed.
  
(** Specification of the compiler for statements *)
Theorem specStmt x q q' s c : x ↓[q] q' -> ⟨compS x c, s, q⟩ 
                                 =>> ⟨c , s, q'⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.

(** Calculation of the compiler for expressions *)

(** - [Put x ↓[q] v]: *)

  begin
    ⟨c, s, v⟩.
  <== {apply vm_put}
    ⟨PUT c, VAL v :: s, q⟩.
  <<= {apply specExpr}
    ⟨compE x (PUT c), s, q⟩.
  [].

(** - [Seqn x1 x2 ↓[q1] q3]: *)
  
  begin
    ⟨c, s, q3⟩.
  <<= {apply IHrun2}
    ⟨compS x2 c, s, q2⟩.
  <<= {apply IHrun1}
    ⟨compS x1 (compS x2 c), s, q1⟩.
  [].

(** - [While x1 x2 ↓[q] q] ([run_while_exit]): *)

  begin
    ⟨c, s, q⟩.
  <== {apply vm_jmp_no}
    ⟨JMP c (compS x2 LOOP), VAL 0 :: CON (compS (While x1 x2) c) :: s, q⟩.
  <<= {apply specExpr}
    ⟨compE x1 (JMP c (compS x2 LOOP)), CON (compS (While x1 x2) c) :: s, q ⟩.
  <== {apply vm_enter}
    ⟨ENTER (compE x1 (JMP c (compS x2 LOOP))), s, q ⟩.
  [].

(** - [While x1 x2 ↓[q1] q3] ([run_while_cont]): *)

  begin
    ⟨c, s, q3⟩.
  <<= {apply IHrun2}
    ⟨compS (While x1 x2) c, s, q2 ⟩.
  <== {apply vm_loop}
    ⟨LOOP, CON (compS (While x1 x2) c) :: s, q2 ⟩.
  <<= {apply IHrun1}
    ⟨compS x2 LOOP, CON (compS (While x1 x2) c) :: s, q1 ⟩.
  <== {apply vm_jmp_yes}
    ⟨JMP c (compS x2 LOOP), VAL v :: CON (compS (While x1 x2) c) :: s, q1 ⟩.
  <<= {apply specExpr}
    ⟨compE x1 (JMP c (compS x2 LOOP)), CON (compS (While x1 x2) c) :: s, q1 ⟩.
  <== {apply vm_enter}
    ⟨ENTER (compE x1 (JMP c (compS x2 LOOP))), s, q1 ⟩.
  [].

Qed.
  
(** * Soundness *)
  
Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; try reflexivity.
  inversion H. inversion H5.
Qed.
  

Definition terminates (x : Stmt) : Prop := exists q, x ↓[0] q.

Theorem sound x C : terminates x -> ⟨comp x, nil, 0⟩ =>>! C -> 
                          exists q, C = ⟨HALT, nil, q⟩ /\ x ↓[0] q.
Proof.
  unfold terminates. intros. destruct H as [q T].
  
  pose (specStmt x 0 q nil HALT) as H'. exists q. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. auto. intro. destruct H. 
  inversion H. assumption.
Qed.
  