(** Calculation of the simple arithmetic language. *)
Require Import List.
Require Import Tactics.

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr.


Fixpoint eval (e: Expr) : nat :=
  match e with
    | Val n => n
    | Add x y => eval x + eval y
  end.

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

Definition Stack : Set := list nat.

Definition Conf : Set := prod Code  Stack.

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : (PUSH n c , s) ==> (c , n :: s)
| vm_add c s m n : (ADD c, m :: n :: s) ==> (c, (n + m) :: s)
where "x ==> y" := (VM x y).

(** Boilerplate to import calculation tactics *)
Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

Theorem spec e c s : (comp' e c, s) =>> (c , eval e :: s).
Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction e;intros.

  begin
  (c, n :: s).
  <== { apply vm_push }
  (PUSH n c, s).
  [].

  begin
  (c, eval e1 + eval e2 :: s).
  <== { apply vm_add}
  (ADD c, eval e2 :: eval e1 :: s).
  <<= { apply IHe2}
  (comp' e2 (ADD c), eval e1 :: s).
  <<= { apply IHe1}
  (comp' e1 (comp' e2 (ADD c)), s).
  [].
Qed.

  
(** Since the VM is defined as a small step operational semantics, we
have to prove that the VM is deterministic and does not get stuck in
order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.


Theorem sound e s C : (comp e, s) =>>! C -> C = (HALT , eval e :: s).
Proof.
  intros.
  pose (spec e HALT) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. intro Contra. destruct Contra.
  inversion H0.
Qed.