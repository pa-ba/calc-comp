(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (x: Expr) : nat :=
  match x with
    | Val n => n
    | Add x1 x2 => eval x1 + eval x2
  end.

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (c : Code) : Code :=
  match x with
    | Val n => PUSH n c
    | Add x1 x2 => comp' x1 (comp' x2 (ADD c))
  end.

Definition comp (x : Expr) : Code := comp' x HALT.

(** * Virtual Machine *)

Definition Stack : Set := list nat.

Definition Conf : Set := prod Code  Stack.

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : (PUSH n c , s) ==> (c , n :: s)
| vm_add c s m n : (ADD c, m :: n :: s) ==> (c, (n + m) :: s)
where "x ==> y" := (VM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec x c s : (comp' x c, s) =>> (c , eval x :: s).

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction x;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
  (c, n :: s).
  <== { apply vm_push }
  (PUSH n c, s).
  [].

(** - [x = Add x1 x2]: *)

  begin
  (c, eval x1 + eval x2 :: s).
  <== { apply vm_add}
  (ADD c, eval x2 :: eval x1 :: s).
  <<= { apply IHx2}
  (comp' x2 (ADD c), eval x1 :: s).
  <<= { apply IHx1}
  (comp' x1 (comp' x2 (ADD c)), s).
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we
have to prove that the VM is deterministic and does not get stuck in
order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.


Theorem sound x s C : (comp x, s) =>>! C -> C = (HALT , eval x :: s).
Proof.
  intros.
  pose (spec x HALT) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. intro Contra. destruct Contra.
  inversion H0.
Qed.