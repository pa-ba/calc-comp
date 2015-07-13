(** Calculation for arithmetic + exceptions + local state. *)

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

Fixpoint eval (x: Expr) (q : State) : option (nat * State) :=
  match x with
    | Val n => Some (n , q)
    | Add x1 x2 => match eval x1 q with
                   | Some (n, q') => match eval x2 q' with
                                     | Some (m, q'') => Some ((n + m), q'')
                                     | None => None
                                     end
                   | None => None
                   end
    | Throw => None
    | Catch x1 x2 => match eval x1 q with
                     | Some (n, q') => Some (n, q')
                     | None => eval x2 q
                     end
    | Get => Some (q, q)
    | Put x1 x2 => match eval x1 q with
                   | Some (n, q') => eval x2 n
                   | None => None
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

Fixpoint comp' (x : Expr) (c : Code) : Code :=
  match x with
    | Val n => PUSH n c
    | Add x1 x2 => comp' x1 (comp' x2 (ADD c))
    | Throw => FAIL
    | Catch x1 x2 => MARK (comp' x2 c) (comp' x1 (UNMARK c))
    | Get => LOAD c
    | Put x1 x2 => comp' x1 (SAVE (comp' x2 c))
  end.

Definition comp (x : Expr) : Code := comp' x HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| HAN : Code -> State -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> State -> Conf
| fail : Stack -> Conf.

Notation "⟨ c , s , q ⟩" := (conf c s q).
Notation "⟪ s ⟫" := (fail s ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s q : ⟨PUSH n c, s, q⟩ ==> ⟨ c , VAL n :: s, q ⟩
| vm_add c s q m n : ⟨ADD c, VAL m :: VAL n :: s, q⟩ ==> ⟨c, VAL (n + m) :: s, q⟩
| vm_fail s q : ⟨ FAIL, s, q⟩ ==> ⟪s⟫
| vm_mark c h s q : ⟨MARK h c, s, q⟩ ==> ⟨c, HAN h q :: s, q⟩
| vm_unmark c n h s q q' : ⟨UNMARK c, VAL n :: HAN h q' :: s, q⟩ ==> ⟨c, VAL n :: s, q⟩
| vm_load c s q : ⟨LOAD c, s, q⟩ ==> ⟨c, VAL q :: s, q⟩
| vm_save c n s q : ⟨SAVE c, VAL n :: s, q⟩ ==> ⟨c, s, n⟩
| vm_fail_val n s : ⟪VAL n :: s ⟫ ==> ⟪s⟫
| vm_fail_han c s q : ⟪HAN c q :: s ⟫ ==> ⟨c, s, q⟩
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

Theorem spec x c s q : ⟨comp' x c, s, q⟩
                       =>> match eval x q with
                            | Some (n, q') => ⟨c , VAL n :: s, q'⟩
                            | None => ⟪s⟫
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent q.
  induction x;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
  ⟨c, VAL n :: s, q⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, q⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
   (match eval x1 q with
     | Some (m, q') => match eval x2 q' with
                         | Some (n, q'') => ⟨ c, VAL (m + n) :: s, q'' ⟩
                         | None => ⟪ s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply vm_add }
   (match eval x1 q with
     | Some (m, q') => match eval x2 q' with
                         | Some (n, q'') => ⟨ ADD c, VAL n :: VAL m :: s, q'' ⟩
                         | None => ⟪ s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply vm_fail_val }
   (match eval x1 q with
     | Some (m, q') => match eval x2 q' with
                         | Some (n, q'') => ⟨ ADD c, VAL n :: VAL m :: s, q'' ⟩
                         | None => ⟪ VAL m :: s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply IHx2 }
   (match eval x1 q with
     | Some (m, q') =>  ⟨ comp' x2 (ADD c), VAL m :: s, q' ⟩
     | None => ⟪ s ⟫
     end).
  <<= { apply IHx1 }
      ⟨ comp' x1 (comp' x2 (ADD c)), s, q ⟩.
  [].

(** - [x = Throw]: *)

  begin
    ⟪s⟫.
  <== { apply vm_fail }
    ⟨ FAIL, s, q⟩.
  [].

(** - [x = Catch x1 x2]: *)

  begin
    (match eval x1 q with
         | Some (m, q') => ⟨ c, VAL m :: s, q'⟩
         | None => match eval x2 q with
                     | Some (n, q'') => ⟨c, VAL n :: s, q''⟩
                     | None => ⟪s⟫
                   end
    end).
   <<= { apply IHx2 }
    (match eval x1 q with
         | Some (m, q') => ⟨ c, VAL m :: s, q'⟩
         | None => ⟨comp' x2 c, s, q⟩
    end).
   <<= { apply vm_fail_han }
    (match eval x1 q with
         | Some (m, q') => ⟨ c, VAL m :: s, q'⟩
         | None => ⟪ HAN (comp' x2 c) q :: s⟫
    end).
   <<= { apply vm_unmark }
    (match eval x1 q with
         | Some (m, q') => ⟨ UNMARK c, VAL m :: HAN (comp' x2 c) q :: s, q'⟩
         | None => ⟪ HAN (comp' x2 c) q :: s⟫
    end).
   <<= { apply IHx1 }
       ⟨ comp' x1 (UNMARK c), HAN (comp' x2 c) q :: s, q⟩.
   <<= { apply vm_mark }
       ⟨ MARK (comp' x2 c) (comp' x1 (UNMARK c)),  s, q⟩.
   [].

(** - [x = Get]: *)

   begin
     ⟨ c, VAL q :: s, q⟩.
   <== { apply vm_load }
     ⟨ LOAD c, s, q⟩.
   [].

(** - [x = Put x1 x2]: *)

   begin
     (match eval x1 q with
          | Some (n, q') => match eval x2 n with
                                | Some (m, q'') => ⟨c, VAL m :: s, q''⟩
                                | None => ⟪s⟫
                            end
          | None => ⟪s⟫
      end).
   <<= { apply IHx2 }
       (match eval x1 q with
          | Some (n, q') => ⟨comp' x2 c, s, n⟩
          | None => ⟪s⟫
        end).
   <<= { apply vm_save }
       (match eval x1 q with
          | Some (n, q') => ⟨SAVE (comp' x2 c), VAL n :: s, q'⟩
          | None => ⟪s⟫
        end).
   <<= { apply IHx1 }
       ⟨comp' x1 (SAVE (comp' x2 c)), s, q⟩.
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
                             | Some (n, q) => ⟨HALT , VAL n :: nil, q⟩
                             | None =>  ⟪nil⟫ 
                           end  ==> C).
Proof.
  destruct x; try destruct p; intro Contra; destruct Contra; subst; inversion H.
Qed.

Theorem sound x C q : ⟨comp x, nil, q⟩ =>>! C -> C = match eval x q with
                                                  | Some (n, q') => ⟨HALT , VAL n :: nil, q'⟩
                                                  | None =>  ⟪nil⟫ 
                                                end.
Proof.
  intros.
  pose (spec x HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.