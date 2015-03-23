(** Calculation for arithmetic + exceptions + global state. *)

Require Import List.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr
| Get : Expr
| Put : Expr -> Expr -> Expr.

(** * Semantics *)

Definition State := nat.

Fixpoint eval (e: Expr) (q : State) : (option nat * State) :=
  match e with
    | Val n => (Some n , q)
    | Add x y => match eval x q with
                   | (Some n, q') => match eval y q' with
                                       | (Some m, q'') => (Some (n + m), q'')
                                       | (None, q'') => (None, q'')
                               end
                   | (None, q') => (None, q')
                 end
    | Throw => (None, q)
    | Catch x y => match eval x q with
                     | (Some n, q') => (Some n, q')
                     | (None, q') => eval y q'
                   end
    | Get => (Some q,q)
    | Put x y => match eval x q with
                     | (Some n, q') => eval y n
                     | (None, q') => (None, q')
                   end
  end.

(** * Compiler *)

Inductive Code : Set :=
| HALT : Code
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| FAIL : Code 
| MARK : Code -> Code -> Code
| UNMARK : Code -> Code
| LOAD : Code -> Code
| SAVE : Code -> Code
.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
    | Throw => FAIL
    | Catch x h => MARK (comp' h c) (comp' x (UNMARK c))
    | Get => LOAD c
    | Put x y => comp' x (SAVE (comp' y c))
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| HAN : Code -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> State -> Conf
| fail : Stack -> State -> Conf.

Notation "⟨ c , s , q ⟩" := (conf c s q).
Notation "⟪ s , q ⟫" := (fail s q ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s q : ⟨PUSH n c, s, q⟩ ==> ⟨ c , VAL n :: s, q ⟩
| vm_add c s q m n : ⟨ADD c, VAL m :: VAL n :: s, q⟩ ==> ⟨c, VAL (n + m) :: s, q⟩
| vm_fail s q : ⟨ FAIL, s, q⟩ ==> ⟪s,q⟫
| vm_mark c h s q : ⟨MARK h c, s, q⟩ ==> ⟨c, HAN h :: s, q⟩
| vm_unmark c n h s q : ⟨UNMARK c, VAL n :: HAN h :: s, q⟩ ==> ⟨c, VAL n :: s, q⟩
| vm_load c s q : ⟨LOAD c, s, q⟩ ==> ⟨c, VAL q :: s, q⟩
| vm_save c n s q : ⟨SAVE c, VAL n :: s, q⟩ ==> ⟨c, s, n⟩
| vm_fail_val n s q : ⟪VAL n :: s, q ⟫ ==> ⟪s, q⟫
| vm_fail_han c s q : ⟪HAN c :: s, q ⟫ ==> ⟨c, s, q⟩
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

Theorem spec e c s q : ⟨comp' e c, s, q⟩
                       =>> match eval e q with
                            | (Some n, q') => ⟨c , VAL n :: s, q'⟩
                            | (None, q') => ⟪ s, q' ⟫
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent q.
  induction e;intros.

(** Calculation of the compiler *)

(** - [e = Val n]: *)

  begin
  ⟨c, VAL n :: s, q⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, q⟩.
  [].

(** - [e = Add e1 e2]: *)
  
  begin
   (match eval e1 q with
     | (Some m, q') => match eval e2 q' with
                         | (Some n, q'') => ⟨ c, VAL (m + n) :: s, q'' ⟩
                         | (None, q'') => ⟪ s, q'' ⟫
                  end
     | (None, q') => ⟪ s, q' ⟫
     end).
  <<= { apply vm_add }
   (match eval e1 q with
     | (Some m, q') => match eval e2 q' with
                         | (Some n, q'') => ⟨ ADD c, VAL n :: VAL m :: s, q'' ⟩
                         | (None, q'') => ⟪ s, q'' ⟫
                  end
     | (None, q') => ⟪ s, q' ⟫
     end).
  <<= { apply vm_fail_val }
   (match eval e1 q with
     | (Some m, q') => match eval e2 q' with
                         | (Some n, q'') => ⟨ ADD c, VAL n :: VAL m :: s, q'' ⟩
                         | (None, q'') => ⟪ VAL m :: s, q'' ⟫
                  end
     | (None, q') => ⟪ s, q' ⟫
     end).
  <<= { apply IHe2 }
   (match eval e1 q with
     | (Some m, q') =>  ⟨ comp' e2 (ADD c), VAL m :: s, q' ⟩
     | (None, q') => ⟪ s, q' ⟫
     end).
  <<= { apply IHe1 }
      ⟨ comp' e1 (comp' e2 (ADD c)), s, q ⟩.
  [].

(** - [e = Throw]: *)

  begin
    ⟪s, q⟫.
  <== { apply vm_fail }
    ⟨ FAIL, s, q⟩.
  [].

(** - [e = Catch e1 e2]: *)

  begin
    (match eval e1 q with
         | (Some m, q') => ⟨ c, VAL m :: s, q'⟩
         | (None, q') => match eval e2 q' with
                           | (Some n, q'') => ⟨c, VAL n :: s, q''⟩
                           | (None, q'') => ⟪s, q''⟫
                         end
    end).
   <<= { apply IHe2 }
    (match eval e1 q with
         | (Some m, q') => ⟨ c, VAL m :: s, q'⟩
         | (None, q') => ⟨comp' e2 c, s, q'⟩
    end).
   <<= { apply vm_fail_han }
    (match eval e1 q with
         | (Some m, q') => ⟨ c, VAL m :: s, q'⟩
         | (None, q') => ⟪ HAN (comp' e2 c) :: s, q'⟫
    end).
   <<= { apply vm_unmark }
    (match eval e1 q with
         | (Some m, q') => ⟨ UNMARK c, VAL m :: HAN (comp' e2 c) :: s, q'⟩
         | (None, q') => ⟪ HAN (comp' e2 c) :: s, q'⟫
    end).
   <<= { apply IHe1 }
       ⟨ comp' e1 (UNMARK c), HAN (comp' e2 c) :: s, q⟩.
   <<= { apply vm_mark }
       ⟨ MARK (comp' e2 c) (comp' e1 (UNMARK c)),  s, q⟩.
   [].

(** - [e = Get]: *)

   begin
     ⟨ c, VAL q :: s, q⟩.
   <== { apply vm_load }
     ⟨ LOAD c, s, q⟩.
   [].

(** - [e = Put e1 e2]: *)

   begin
     (match eval e1 q with
          | (Some n, q') => match eval e2 n with
                                | (Some m, q'') => ⟨c, VAL m :: s, q''⟩
                                | (None, q'') => ⟪s, q''⟫
                            end
          | (None, q') => ⟪s, q'⟫
      end).
   <<= { apply IHe2 }
       (match eval e1 q with
          | (Some n, q') => ⟨comp' e2 c, s, n⟩
          | (None, q') => ⟪s, q'⟫
        end).
   <<= { apply vm_save }
       (match eval e1 q with
          | (Some n, q') => ⟨SAVE (comp' e2 c), VAL n :: s, q'⟩
          | (None, q') => ⟪s, q'⟫
        end).
   <<= { apply IHe1 }
       ⟨comp' e1 (SAVE (comp' e2 c)), s, q⟩.
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
                             | (Some n, q) => ⟨HALT , VAL n :: nil, q⟩
                             | (None, q) =>  ⟪nil, q⟫ 
                           end  ==> C).
Proof.
  destruct x; destruct o; intro Contra; destruct Contra; subst; inversion H.
Qed.

Theorem sound e C q : ⟨comp e, nil, q⟩ =>>! C -> C = match eval e q with
                                                  | (Some n, q') => ⟨HALT , VAL n :: nil, q'⟩
                                                  | (None, q') =>  ⟪nil, q'⟫ 
                                                end.
Proof.
  intros.
  pose (spec e HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.