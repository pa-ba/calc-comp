(** Calculation for arithmetic + exceptions with two continuations. *)

Require Import List.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (e: Expr) : option nat :=
  match e with
    | Val n => Some n
    | Add x y => match eval x with
                   | Some n => match eval y with
                                 | Some m => Some (n + m)
                                 | None => None
                               end
                   | None => None
                 end
    | Throw => None
    | Catch x y => match eval x with
                     | Some n => Some n
                     | None => eval y
                   end
  end.

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| POP : Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (sc : Code) (fc : Code) : Code :=
  match e with
    | Val n =>  PUSH n sc
    | Add x y => comp' x (comp' y (ADD sc) (POP fc)) fc 
    | Throw => fc
    | Catch x h => comp' x sc (comp' h sc fc)
  end.

Definition comp (e : Expr) : Code := comp' e HALT HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Conf.

Notation "⟨ x , y ⟩" := (conf x y).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : ⟨PUSH n c, s⟩ ==> ⟨ c , VAL n :: s ⟩
| vm_add c s m n : ⟨ADD c, VAL m :: VAL n :: s⟩ ==> ⟨c, VAL (n + m) :: s⟩
| vm_pop c n s : ⟨POP c, VAL n :: s⟩ ==> ⟨c, s⟩
where "x ==> y" := (VM x y).

Hint Constructors VM.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec e sc fc s : ⟨comp' e sc fc, s⟩
                       =>> match eval e with
                            | Some n => ⟨sc , VAL n :: s⟩
                            | None => ⟨fc , s⟩
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent sc.
  generalize dependent fc.
  generalize dependent s.
  induction e;intros.

(** Calculation of the compiler *)

(** - [e = Val n]: *)

  begin
  ⟨sc, VAL n :: s⟩.
  <== { apply vm_push }
  ⟨PUSH n sc, s⟩.
  [].

(** - [e = Add e1 e2]: *)
  
  begin
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ sc, VAL (m + n) :: s ⟩
                  | None => ⟨ fc, s ⟩
                  end
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply vm_add }
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ ADD sc, VAL n :: VAL m :: s ⟩
                  | None => ⟨ fc, s ⟩
                  end
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply vm_pop }
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ ADD sc, VAL n :: VAL m :: s ⟩
                  | None => ⟨ POP fc, VAL m :: s ⟩
                  end
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply IHe2 }
   (match eval e1 with
     | Some m =>  ⟨ (comp' e2 (ADD sc) (POP fc)), VAL m :: s⟩
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply IHe1 }
      ⟨ comp' e1 (comp' e2 (ADD sc) (POP fc)) fc, s ⟩.
  [].

(** - [e = Throw]: *)

  begin
    ⟨ fc, s⟩.
  [].

(** - [e = Catch e1 e2]: *)

  begin
    (match eval e1 with
         | Some m => ⟨ sc, VAL m :: s⟩
         | None => match eval e2 with
                     | Some n => ⟨sc, VAL n :: s⟩
                     | None => ⟨fc, s⟩
                   end
    end).
   <<= { apply IHe2 }
    (match eval e1 with
         | Some m => ⟨ sc, VAL m :: s⟩
         | None => ⟨comp' e2 sc fc, s⟩
    end).
   <<= { apply IHe1 }
       ⟨ comp' e1 sc (comp' e2 sc fc) , s⟩.
   [].
Qed.

(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we
have to prove that the VM is deterministic and does not get stuck in
order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.
  
Lemma term_vm x :  ~ (exists C, match x with
                             | Some n => ⟨HALT , VAL n :: nil⟩
                             | None =>  ⟨HALT , nil⟩
                           end  ==> C).
Proof.
  destruct x; intro Contra; destruct Contra; subst; inversion H.
Qed.



Theorem sound e C : ⟨comp e, nil⟩ =>>! C -> C = match eval e with
                                                  | Some n => ⟨HALT , VAL n :: nil⟩
                                                  | None =>  ⟨HALT , nil⟩
                                                end.
Proof.
  intros.
  pose (spec e HALT HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.