(** Calculation of a compiler for the call-by-value lambda calculus +
arithmetic + exceptions. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw :  Expr 
| Catch : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> list Value -> Value.

Definition Env := list Value.

Reserved Notation "x ⇓[ e ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> option Value -> Prop :=
| eval_val e n : Val n ⇓[e] Some (Num n)
| eval_add e x y m n : x ⇓[e] m -> y ⇓[e] n 
                       -> Add x y ⇓[e] (match m, n with
                                          | Some (Num m'), Some (Num n') => Some (Num (m' + n'))
                                          | _,_ => None
                                        end  )
| eval_throw e : Throw ⇓[e] None
| eval_catch e x y m n : x ⇓[e] m -> y ⇓[e] n 
                       -> Catch x y ⇓[e] (match m with
                                            | None => n
                                            | _ => m
                                        end  )
| eval_var e i : Var i ⇓[e] nth e i
| eval_abs e x : Abs x ⇓[e] Some (Clo x e)
| eval_app e  x x'' y  x' e' y' : x ⇓[e] Some (Clo x' e') -> y ⇓[e] Some y' -> x' ⇓[y' :: e'] x''
                                -> App x y ⇓[e] x''
| eval_app_fail x x' y y' e : x ⇓[e] x' -> y ⇓[e] y' -> 
                              (x' = None \/ exists n, x' = Some (Num n) \/ y' = None) -> 
                              App x y ⇓[e] None
where "x ⇓[ e ] y" := (eval x e y).

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| LOOKUP : nat -> Code -> Code
| RET : Code
| APP : Code -> Code
| ABS : Code -> Code -> Code
| ASSERT_NUM : Code -> Code
| ASSERT_CLO : Code -> Code
| UNMARK : Code -> Code
| MARK : Code -> Code -> Code
| FAIL : Code
| HALT : Code.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (ASSERT_NUM (comp' y (ADD c)))
    | Var i => LOOKUP i c
    | App x y => comp' x (ASSERT_CLO (comp' y (APP c)))
    | Abs x => ABS (comp' x RET) c
    | Throw => FAIL
    | Catch x y => MARK (comp' y c) (comp' x (UNMARK c))
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Exc' : Value'
| Clo' : Code -> list Value' -> Value'.

Definition Env' := list Value'.

Inductive Elem : Set :=
| VAL : Value' -> Elem 
| HAN : Code -> Elem 
| CLO : Code -> Env' -> Elem
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Env' -> Conf
| fail : Stack -> Env' -> Conf.

Notation "⟨ x , y , e ⟩" := (conf x y e).
Notation "⟪ x , e ⟫" := (fail x e ).

Reserved Notation "x ==> y" (at level 80, no associativity).

Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s e :  ⟨PUSH n c, s, e⟩ ==> ⟨c, VAL (Num' n) :: s, e⟩
| vm_add c m n s e : ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, e⟩ 
                       ==> ⟨c, VAL (Num'(m + n)) :: s, e⟩
| vm_lookup e i c v s : nth e i = Some v -> ⟨LOOKUP i c, s, e ⟩ ==> ⟨c, VAL v :: s, e ⟩
| vm_lookup_fail e i c s : nth e i = None -> ⟨LOOKUP i c, s, e ⟩ ==> ⟪s, e ⟫
| vm_env v c e e' s  : ⟨RET, VAL v :: CLO c e :: s, e'⟩ ==> ⟨c, VAL v :: s, e⟩
| vm_fail_env c e e' s  : ⟪CLO c e :: s, e'⟫ ==> ⟪s, e⟫
| vm_app c c' e e' v s : ⟨APP c, VAL v :: VAL (Clo' c' e') :: s, e⟩
              ==> ⟨c', CLO c e :: s, v :: e'⟩
| vm_abs c c' s e : ⟨ABS c' c, s, e ⟩ ==> ⟨c, VAL (Clo' c' e) :: s, e ⟩
| vm_fail_val s e v : ⟪ VAL v :: s, e ⟫ ==> ⟪ s, e ⟫
| vm_fail_han c s e : ⟪HAN c :: s, e ⟫ ==> ⟨c, s, e⟩
| vm_fail s e : ⟨ FAIL, s, e ⟩ ==> ⟪ s, e ⟫
| vm_add_fail s c c' e e' m : ⟨ADD c, VAL (Clo' c' e') :: VAL (Num' m) :: s, e⟩ ==> ⟪s, e⟫
| vm_unmark c n h s e : ⟨UNMARK c, VAL n :: HAN h :: s, e⟩ ==> ⟨c, VAL n :: s, e⟩
| vm_mark c h s e : ⟨MARK h c, s, e⟩ ==> ⟨c, HAN h :: s, e⟩
| vm_assert_num s c e n :  ⟨ASSERT_NUM c, VAL (Num' n) :: s, e⟩ ==> ⟨c, VAL (Num' n) :: s, e⟩
| vm_assert_num_fail s c e c' e' :  ⟨ASSERT_NUM c, VAL (Clo' c' e') :: s, e⟩ ==> ⟪s, e⟫
| vm_assert_clo s c e c' e' :  ⟨ASSERT_CLO c, VAL (Clo' c' e') :: s, e⟩ ==> ⟨c, VAL (Clo' c' e') :: s, e⟩
| vm_assert_clo_fail s c e n :  ⟨ASSERT_CLO c, VAL (Num' n) :: s, e⟩ ==> ⟪s, e⟫
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Clo x e => Clo' (comp' x RET) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec p e r c s : p ⇓[e] r -> ⟨comp' p c, s, convE e⟩ 
                                 =>> match r with 
                                       | Some r' => ⟨c , VAL (conv r') :: s, convE e⟩
                                       | None => ⟪s, convE e⟫
                                     end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, VAL (Num' n) :: s, convE e⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, convE e⟩.
  [].

(** - [Add x y ⇓[e] Num (m + n)]: *)

  begin
    match m, n with
       | Some (Num m'), Some (Num n') => ⟨c, VAL (Num' (m' + n')) :: s, convE e ⟩
       | _ , _ => ⟪ s , convE e ⟫
     end.
  <<= {apply vm_add}
    match m, n with
       | Some (Num m'), Some (Num n') => ⟨ADD c, VAL (Num' n') :: VAL (Num' m') :: s, convE e ⟩
       | _ , _ => ⟪ s , convE e ⟫
     end.
  = {auto}
   match m with
       | Some (Num m') => match n with 
                            | Some v => match v with
                                            | Num n' => ⟨ADD c, VAL (Num' n') :: VAL (Num' m') :: s, convE e ⟩
                                            | _ => ⟪s, convE e ⟫
                                        end
                            | None => ⟪ s , convE e ⟫
                          end
       | _ => ⟪ s , convE e ⟫
     end.
  <<= {apply vm_add_fail}
    match m with
       | Some (Num m') => match n with 
                            | Some v => ⟨ADD c, VAL (conv v) :: VAL (Num' m') :: s, convE e ⟩
                            | None => ⟪ s , convE e ⟫
                          end
       | _ => ⟪ s , convE e ⟫
     end.
  <<= {apply vm_fail_val}
    match m with
       | Some (Num m') => match n with 
                            | Some v => ⟨ADD c, VAL (conv v) :: VAL (Num' m') :: s, convE e ⟩
                            | None => ⟪ VAL (Num' m') :: s , convE e ⟫
                          end
       | _ => ⟪ s , convE e ⟫
     end.
  <<= { apply IHeval2 }
    match m with
       | Some (Num m') => ⟨comp' y (ADD c), VAL (Num' m') :: s, convE e ⟩
       | _ => ⟪ s , convE e ⟫
     end.
  = { auto }
    match m with
       | Some v => match v with
                     | Num m' => ⟨comp' y (ADD c), VAL (Num' m') :: s, convE e ⟩
                     | _ => ⟪ s , convE e ⟫
                   end
       | _ => ⟪ s , convE e ⟫
     end.
  <<= { first [apply vm_assert_num| apply vm_assert_num_fail] }
    (match m with
       | Some v => ⟨ASSERT_NUM (comp' y (ADD c)), VAL (conv v) :: s, convE e ⟩
       | _ => ⟪ s , convE e ⟫
     end).
  <<= { apply IHeval1 }
  ⟨comp' x (ASSERT_NUM (comp' y (ADD c))), s, convE e⟩.
  [].

(** - [Throw ⇓[e] v] *)
  begin
    ⟪s, convE e ⟫.
  <== {apply vm_fail}
     ⟨FAIL, s, convE e⟩.  
  [].

(** - [Catch x y ⇓[e] v] *)
  begin
    match m with
      | Some r => ⟨c, VAL (conv r) :: s, convE e ⟩
      | None => match n with
                  | Some r => ⟨c, VAL (conv r) :: s, convE e ⟩
                  | None => ⟪s, convE e ⟫
                end
    end.
  <<= {apply IHeval2}
    match m with
      | Some r => ⟨c, VAL (conv r) :: s, convE e ⟩
      | None =>  ⟨comp' y c, s, convE e ⟩
    end.
  <<= {apply vm_fail_han}
    match m with
      | Some r => ⟨c, VAL (conv r) :: s, convE e ⟩
      | None =>  ⟪ HAN (comp' y c) :: s, convE e ⟫
    end.
  <<= {apply vm_unmark}
    match m with
      | Some r => ⟨UNMARK c, VAL (conv r) :: HAN (comp' y c) :: s, convE e ⟩
      | None =>  ⟪ HAN (comp' y c) :: s, convE e ⟫
    end.
  <<= {apply IHeval1}
      ⟨comp' x (UNMARK c),HAN (comp' y c) :: s, convE e ⟩.
  <<= {apply vm_mark}
      ⟨MARK (comp' y c) (comp' x (UNMARK c)),s, convE e ⟩.
  [].


(** - [Var i ⇓[e] v] *)

  begin
    match nth e i with
      | Some r' => ⟨c, VAL (conv r') :: s, convE e ⟩
      | None => ⟪s, convE e ⟫
    end.
  <== {first[apply vm_lookup|apply vm_lookup_fail]; unfold convE; rewrite nth_map}
    ⟨LOOKUP i c, s, convE e ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, VAL (Clo' (comp' x RET) (convE e)) :: s, convE e ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp' x RET) c, s, convE e ⟩.
  [].

(** - [App x y ⇓[e] x''] *)
  begin
    match x'' with
      | Some r' => ⟨c, VAL (conv r') :: s, convE e ⟩
      | None => ⟪s, convE e ⟫
    end.
  <== { first[apply vm_env|apply vm_fail_env] }
    match x'' with
      | Some r' => ⟨RET, VAL (conv r') :: CLO c (convE e) :: s, convE (y' :: e') ⟩
      | None => ⟪CLO c (convE e) :: s, convE (y' :: e') ⟫
    end.
  <<= { apply IHeval3 }
      ⟨comp' x' RET, CLO c (convE e) :: s, convE (y' :: e') ⟩.
  = {reflexivity}
    ⟨comp' x' RET, CLO c (convE e) :: s, conv y' :: convE e' ⟩.
  <== { apply vm_app }
    ⟨APP c, VAL (conv y') :: VAL (Clo' (comp' x' RET) (convE e')) :: s, convE e ⟩.
  <<= { apply IHeval2 }
    ⟨comp' y (APP c), VAL (Clo' (comp' x' RET) (convE e')) :: s, convE e ⟩.
  = {reflexivity}
    ⟨comp' y (APP c), VAL (conv (Clo x' e')) :: s, convE e ⟩.
  <== {apply vm_assert_clo}
    ⟨ASSERT_CLO (comp' y (APP c)), VAL (conv (Clo x' e')) :: s, convE e ⟩.
  <<= { apply IHeval1 }
    ⟨comp' x (ASSERT_CLO (comp' y (APP c))), s, convE e ⟩.
  [].

  begin
    ⟪s, convE e ⟫.
  = {reflexivity}
      match x' with
        | Some (Clo x'' e') => match y' with 
                                 | Some r => ⟨ APP c, VAL (conv r) :: VAL (conv (Clo x'' e')) :: s, convE e ⟩
                                 | None => ⟪s, convE e ⟫
                               end
        | _ => ⟪s, convE e ⟫
      end.
  <<= {apply vm_fail_val}
      match x' with
        | Some (Clo x'' e') => match y' with 
                                 | Some r => ⟨ APP c, VAL (conv r) :: VAL (conv (Clo x'' e')) :: s, convE e ⟩
                                 | None => ⟪VAL (conv (Clo x'' e')) :: s, convE e ⟫
                               end
        | _ => ⟪s, convE e ⟫
      end.
  <<= {apply IHeval2}
      match x' with
        | Some (Clo x'' e') => ⟨comp' y (APP c), VAL (conv (Clo x'' e')) :: s, convE e ⟩
        | _ => ⟪s, convE e ⟫
      end.
  = {reflexivity}
      match x' with
        | Some v => match v with
                      | Clo x'' e' => ⟨comp' y (APP c), VAL (conv v) :: s, convE e ⟩
                      | Num n => ⟪s, convE e ⟫
                    end
        | _ => ⟪s, convE e ⟫
      end.
  <<= {first [apply vm_assert_clo_fail| apply vm_assert_clo]}
      match x' with
        | Some v => ⟨ASSERT_CLO (comp' y (APP c)), VAL (conv v) :: s, convE e ⟩
        | _ => ⟪s, convE e ⟫
      end.
  <<= {apply IHeval1}
      ⟨comp' x (ASSERT_CLO (comp' y (APP c))), s, convE e ⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; first [reflexivity|congruence].
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p C : terminates p -> ⟨comp p, nil, nil⟩ =>>! C -> 
                          (exists r, C = ⟨HALT , VAL (conv r) :: nil, nil⟩ /\ p ⇓[nil] Some r)
                          \/ (C = ⟪ nil, nil⟫ /\ p ⇓[nil] None).
Proof.
  unfold terminates. intros. destruct H as [r T].
  pose (spec p nil r HALT nil) as H'.
  pose (determ_trc determ_vm) as D. unfold determ in D. 
  destruct r.
  - left. eexists. split. eapply D. eassumption. split. auto. intro. destruct H. 
    inversion H. assumption.
  - right. split. eapply D. eassumption. split. auto. intro. destruct H. inversion H. assumption.
Qed.
  