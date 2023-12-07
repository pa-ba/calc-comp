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

Fixpoint eval (x: Expr) : option nat :=
  match x with
    | Val n => Some n
    | Add x1 x2 => match eval x1 with
                   | Some n => match eval x2 with
                                 | Some m => Some (n + m)
                                 | None => None
                               end
                   | None => None
                   end
    | Throw => None
    | Catch x1 x2 => match eval x1 with
                     | Some n => Some n
                     | None => eval x2
                     end
  end.

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| POP : Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (sc : Code) (fc : Code) : Code :=
  match x with
    | Val n =>  PUSH n sc
    | Add x y => comp' x (comp' y (ADD sc) (POP fc)) fc 
    | Throw => fc
    | Catch x1 x2 => comp' x1 sc (comp' x2 sc fc)
  end.

Definition comp (x : Expr) : Code := comp' x HALT HALT.

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

#[export]
Hint Constructors VM : core.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec x sc fc s : ⟨comp' x sc fc, s⟩
                       =>> match eval x with
                            | Some n => ⟨sc , VAL n :: s⟩
                            | None => ⟨fc , s⟩
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent sc.
  generalize dependent fc.
  generalize dependent s.
  induction x;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
  ⟨sc, VAL n :: s⟩.
  <== { apply vm_push }
  ⟨PUSH n sc, s⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
   (match eval x1 with
     | Some m => match eval x2 with
                  | Some n => ⟨ sc, VAL (m + n) :: s ⟩
                  | None => ⟨ fc, s ⟩
                  end
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply vm_add }
   (match eval x1 with
     | Some m => match eval x2 with
                  | Some n => ⟨ ADD sc, VAL n :: VAL m :: s ⟩
                  | None => ⟨ fc, s ⟩
                  end
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply vm_pop }
   (match eval x1 with
     | Some m => match eval x2 with
                  | Some n => ⟨ ADD sc, VAL n :: VAL m :: s ⟩
                  | None => ⟨ POP fc, VAL m :: s ⟩
                  end
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply IHx2 }
   (match eval x1 with
     | Some m =>  ⟨ (comp' x2 (ADD sc) (POP fc)), VAL m :: s⟩
     | None => ⟨ fc, s ⟩
     end).
  <<= { apply IHx1 }
      ⟨ comp' x1 (comp' x2 (ADD sc) (POP fc)) fc, s ⟩.
  [].

(** - [x = Throw]: *)

  begin
    ⟨ fc, s⟩.
  [].

(** - [x = Catch x1 x2]: *)

  begin
    (match eval x1 with
         | Some m => ⟨ sc, VAL m :: s⟩
         | None => match eval x2 with
                     | Some n => ⟨sc, VAL n :: s⟩
                     | None => ⟨fc, s⟩
                   end
    end).
   <<= { apply IHx2 }
    (match eval x1 with
         | Some m => ⟨ sc, VAL m :: s⟩
         | None => ⟨comp' x2 sc fc, s⟩
    end).
   <<= { apply IHx1 }
       ⟨ comp' x1 sc (comp' x2 sc fc) , s⟩.
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



Theorem sound x C : ⟨comp x, nil⟩ =>>! C -> C = match eval x with
                                                  | Some n => ⟨HALT , VAL n :: nil⟩
                                                  | None =>  ⟨HALT , nil⟩
                                                end.
Proof.
  intros.
  pose (spec x HALT HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.
