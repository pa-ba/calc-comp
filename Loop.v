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
| run_put e q v : e ⇓[q] v -> Put e ↓[q] v
| run_seqn e1 e2 q1 q2 q3 : e1 ↓[q1] q2 -> e2 ↓[q2] q3 -> Seqn e1 e2 ↓[q1] q3
| run_while_exit e1 e2 q : e1 ⇓[q] 0 -> While e1 e2 ↓[q] q
| run_while_cont v e1 e2 q1 q2 q3 : e1 ⇓[q1] v -> v > 0 -> e2 ↓[q1] q2 -> While e1 e2 ↓[q2] q3 
                   -> While e1 e2 ↓[q1] q3
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

Fixpoint compE (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => compE x (compE y (ADD c))
    | Get => GET c
  end.

Fixpoint compS (e : Stmt) (c : Code) : Code :=
  match e with
    | Put e => compE e (PUT c)
    | Seqn e1 e2 => compS e1 (compS e2 c)
    | While e1 e2 => ENTER (compE e1 (JMP c (compS e2 LOOP)))
  end.

Definition comp (e : Stmt) : Code := compS e HALT.

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
Theorem specExpr e q v s c : e ⇓[q] v -> ⟨compE e c, s, q⟩ 
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
Theorem specStmt e q q' s c : e ↓[q] q' -> ⟨compS e c, s, q⟩ 
                                 =>> ⟨c , s, q'⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.

(** Calculation of the compiler for expressions *)

(** - [Put e ↓[q] v]: *)

  begin
    ⟨c, s, v⟩.
  <== {apply vm_put}
    ⟨PUT c, VAL v :: s, q⟩.
  <<= {apply specExpr}
    ⟨compE e (PUT c), s, q⟩.
  [].

(** - [Seqn e1 e2 ↓[q1] q3]: *)
  
  begin
    ⟨c, s, q3⟩.
  <<= {apply IHrun2}
    ⟨compS e2 c, s, q2⟩.
  <<= {apply IHrun1}
    ⟨compS e1 (compS e2 c), s, q1⟩.
  [].

(** - [While e1 e2 ↓[q] q] ([run_while_exit]): *)

  begin
    ⟨c, s, q⟩.
  <== {apply vm_jmp_no}
    ⟨JMP c (compS e2 LOOP), VAL 0 :: CON (compS (While e1 e2) c) :: s, q⟩.
  <<= {apply specExpr}
    ⟨compE e1 (JMP c (compS e2 LOOP)), CON (compS (While e1 e2) c) :: s, q ⟩.
  <== {apply vm_enter}
    ⟨ENTER (compE e1 (JMP c (compS e2 LOOP))), s, q ⟩.
  [].

(** - [While e1 e2 ↓[q1] q3] ([run_while_cont]): *)

  begin
    ⟨c, s, q3⟩.
  <<= {apply IHrun2}
    ⟨compS (While e1 e2) c, s, q2 ⟩.
  <== {apply vm_loop}
    ⟨LOOP, CON (compS (While e1 e2) c) :: s, q2 ⟩.
  <<= {apply IHrun1}
    ⟨compS e2 LOOP, CON (compS (While e1 e2) c) :: s, q1 ⟩.
  <== {apply vm_jmp_yes}
    ⟨JMP c (compS e2 LOOP), VAL v :: CON (compS (While e1 e2) c) :: s, q1 ⟩.
  <<= {apply specExpr}
    ⟨compE e1 (JMP c (compS e2 LOOP)), CON (compS (While e1 e2) c) :: s, q1 ⟩.
  <== {apply vm_enter}
    ⟨ENTER (compE e1 (JMP c (compS e2 LOOP))), s, q1 ⟩.
  [].

Qed.
  
(** * Soundness *)
  
Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; try reflexivity.
  inversion H. inversion H5.
Qed.
  

Definition terminates (e : Stmt) : Prop := exists q, e ↓[0] q.

Theorem sound e C : terminates e -> ⟨comp e, nil, 0⟩ =>>! C -> 
                          exists q, C = ⟨HALT, nil, q⟩ /\ e ↓[0] q.
Proof.
  unfold terminates. intros. destruct H as [q T].
  
  pose (specStmt e 0 q nil HALT) as H'. exists q. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. auto. intro. destruct H. 
  inversion H. assumption.
Qed.
  