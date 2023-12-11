(** Calculation for arithmetic + exceptions. *)

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
| FAIL : Code
| UNMARK : Code -> Code
| MARK : Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (c : Code) : Code :=
  match x with
    | Val n => PUSH n c
    | Add x1 x2 => comp' x1 (comp' x2 (ADD c))
    | Throw => FAIL
    | Catch x1 x2 => MARK (comp' x2 c) (comp' x1 (UNMARK c))
  end.

Definition comp (x : Expr) : Code := comp' x HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| HAN : Code -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Conf
| fail : Stack -> Conf.

Notation "⟨ x , y ⟩" := (conf x y).
Notation "⟪ x ⟫" := (fail x ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : ⟨PUSH n c, s⟩ ==> ⟨ c , VAL n :: s ⟩
| vm_add c s m n : ⟨ADD c, VAL m :: VAL n :: s⟩ ==> ⟨c, VAL (n + m) :: s⟩
| vm_fail_val n s : ⟪VAL n :: s ⟫ ==> ⟪s⟫
| vm_fail s : ⟨ FAIL, s⟩ ==> ⟪s⟫
| vm_fail_han c s : ⟪HAN c :: s ⟫ ==> ⟨c, s⟩
| vm_unmark c n h s : ⟨UNMARK c, VAL n :: HAN h :: s⟩ ==> ⟨c, VAL n :: s⟩
| vm_mark c h s : ⟨MARK h c, s⟩ ==> ⟨c, HAN h :: s⟩
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

Theorem spec x c s : ⟨comp' x c, s⟩
                       =>> match eval x with
                            | Some n => ⟨c , VAL n :: s⟩
                            | None => ⟪ s ⟫
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction x;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
  ⟨c, VAL n :: s⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s⟩.
  [].

(** - [x = Add x1 x2]: *)

  begin
   (match eval x1 with
     | Some m => match eval x2 with
                  | Some n => ⟨ c, VAL (m + n) :: s ⟩
                  | None => ⟪ s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply vm_add }
   (match eval x1 with
     | Some m => match eval x2 with
                  | Some n => ⟨ ADD c, VAL n :: VAL m :: s ⟩
                  | None => ⟪ s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply vm_fail_val }
   (match eval x1 with
     | Some m => match eval x2 with
                  | Some n => ⟨ ADD c, VAL n :: VAL m :: s ⟩
                  | None => ⟪ VAL m :: s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply IHx2 }
   (match eval x1 with
     | Some m =>  ⟨ comp' x2 (ADD c), VAL m :: s ⟩
     | None => ⟪ s ⟫
     end).
  <<= { apply IHx1 }
      ⟨ comp' x1 (comp' x2 (ADD c)), s ⟩.
  [].

(** - [e = Throw]: *)

  begin
    ⟪s⟫.
  <== { apply vm_fail }
    ⟨ FAIL, s⟩.
  [].

(** - [e = Catch x1 x2]: *)

  begin
    (match eval x1 with
         | Some m => ⟨ c, VAL m :: s⟩
         | None => match eval x2 with
                     | Some n => ⟨c, VAL n :: s⟩
                     | None => ⟪s⟫
                   end
    end).
   <<= { apply IHx2 }
    (match eval x1 with
         | Some m => ⟨ c, VAL m :: s⟩
         | None => ⟨comp' x2 c, s⟩
    end).
   <<= { apply vm_fail_han }
    (match eval x1 with
         | Some m => ⟨ c, VAL m :: s⟩
         | None => ⟪ HAN (comp' x2 c) :: s⟫
    end).
   <<= { apply vm_unmark }
    (match eval x1 with
         | Some m => ⟨ UNMARK c, VAL m :: HAN (comp' x2 c) :: s⟩
         | None => ⟪ HAN (comp' x2 c) :: s⟫
    end).
   <<= { apply IHx1 }
       ⟨ comp' x1 (UNMARK c), HAN (comp' x2 c) :: s⟩.
   <<= { apply vm_mark }
       ⟨ MARK (comp' x2 c) (comp' x1 (UNMARK c)),  s⟩.
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
                             | None =>  ⟪nil⟫ 
                           end  ==> C).
Proof.
  destruct x; intro Contra; destruct Contra; subst; inversion H.
Qed.

Theorem sound x C : ⟨comp x, nil⟩ =>>! C -> C = match eval x with
                                                  | Some n => ⟨HALT , VAL n :: nil⟩
                                                  | None =>  ⟪nil⟫ 
                                                end.
Proof.
  intros.
  pose (spec x HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.
