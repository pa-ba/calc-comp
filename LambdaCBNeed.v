(* Calculation of a compiler for the lambda calculus + arithmetic. *)
Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Heap.

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

Definition Env : Set := list Loc.

Inductive Value : Set :=
| Num : nat -> Value
| Fun : Expr -> Env -> Value.

Inductive HElem : Set  :=
  | thunk : Expr -> Env -> HElem
  | value : Value -> HElem.


Definition Heap := Heap.Heap HElem.

Reserved Notation "x ⇓[ e , h , h' ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Heap -> Heap -> Value -> Prop :=
| eval_val e n (h h' : Heap) : Val n ⇓[e,h,h] Num n
| eval_add e x y m n h h' h'' : x ⇓[e,h,h'] Num m -> y ⇓[e,h',h''] Num n -> Add x y ⇓[e,h,h''] Num (m + n)
| eval_var_thunk e e' x i l v h h' : nth e i = Some l -> deref h l = Some (thunk x e') -> x ⇓[e',h,h'] v -> 
                          Var i ⇓[e,h,update h' l (value v)] v
| eval_var_val e i l v h : nth e i = Some l -> deref h l = Some (value v) -> 
                          Var i ⇓[e,h,h] v
| eval_abs e x h : Abs x ⇓[e,h,h] Fun x e
| eval_app e e' x x' x'' y l h h' h'' h''' : x ⇓[e,h,h'] Fun x' e' -> alloc h' (thunk y e) = (h'',l) ->
                              x' ⇓[l :: e',h'',h'''] x'' -> App x y ⇓[e,h,h'''] x''
where "x ⇓[ e , h , h' ] y" := (eval x e h h' y).

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| WRITE : Code
| LOOKUP : nat -> Code -> Code
| RET : Code
| APP : Code -> Code -> Code
| ABS : Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
    | Var i => LOOKUP i c
    | App x y => comp' x (APP (comp' y WRITE) c)
    | Abs x => ABS (comp' x RET) c
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

Inductive Value' : Set :=
| Num' : nat -> Value'
| Fun' : Code -> Env -> Value'.

Inductive HElem' : Set  :=
  | thunk' : Code -> Env -> HElem'
  | value' : Value' -> HElem'.

Definition Heap' := Heap.Heap HElem'.



Inductive Elem : Set :=
| VAL : Value' -> Elem 
| THU : Loc -> Code -> Env -> Elem
| FUN : Code -> Env -> Elem
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Env -> Heap' -> Conf.

Notation "⟨ x , y , e , h ⟩" := (conf x y e h).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s e h :  ⟨PUSH n c, s, e, h⟩ ==> ⟨c, VAL (Num' n) :: s, e, h⟩
| vm_add c m n s e h : ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, e, h⟩
                       ==> ⟨c, VAL (Num'(m + n)) :: s, e, h⟩
| vm_write e e' l v c s h : ⟨WRITE, VAL v :: THU l c e :: s, e', h⟩ ==> ⟨c, VAL v :: s,e,update h l (value' v)⟩
| vm_lookup_thunk e e' i c c' h l s : nth e i = Some l -> deref h l = Some (thunk' c' e') ->
                               ⟨LOOKUP i c, s, e, h⟩ ==> ⟨c', THU l c e :: s, e', h⟩
| vm_lookup_value e i c h l v s : nth e i = Some l -> deref h l = Some (value' v) ->
                               ⟨LOOKUP i c, s, e, h⟩ ==> ⟨c, VAL v :: s, e, h⟩
| vm_ret v c e e' h s  : ⟨RET, VAL v :: FUN c e :: s, e', h⟩ ==> ⟨c, VAL v :: s, e, h⟩
| vm_app c c' c'' e e' s h h' l : alloc h (thunk' c' e) = (h',l) -> 
                           ⟨APP c' c, VAL (Fun' c'' e') :: s, e, h⟩
                            ==> ⟨c'', FUN c e :: s, l :: e', h'⟩
| vm_abs c c' s e h : ⟨ABS c' c, s, e, h⟩ ==> ⟨c, VAL (Fun' c' e) :: s, e, h⟩ 
where "x ==> y" := (VM x y).


Fixpoint convV (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Fun x e => Fun' (comp' x RET) e
  end.

Fixpoint convHE (t : HElem) : HElem' :=
  match t with
    | value v => value' (convV v)
    | thunk x e => thunk' (comp' x WRITE) e
  end.

Definition convH : Heap -> Heap' := hmap convHE.


(* Boilerplate to import calculation tactics *)
Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

Theorem spec p e r c s h h' : p ⇓[e,h,h'] r -> ⟨comp' p c, s, e, convH h⟩ 
                                 =>> ⟨c , VAL (convV r) :: s, e, convH h'⟩.
Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.


  begin
  ⟨c, VAL (Num' n) :: s, e, convH h⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, e, convH h⟩.
  [].

  begin
    ⟨c, VAL (Num' (m + n)) :: s, e, convH h'' ⟩.
  <== { apply vm_add }
    ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, e, convH h''⟩. 
  <<= { apply IHeval2 }
  ⟨comp' y (ADD c), VAL (Num' m) :: s, e, convH h'⟩.
  <<= { apply IHeval1 }
  ⟨comp' x (comp' y (ADD c)), s, e, convH h⟩.
  [].


  assert (deref (convH h) l = Some (thunk' (comp' x WRITE) e'))
    by (unfold convH; rewrite hmap_deref; rewrite H0; reflexivity).
  begin
    ⟨c, VAL (convV v) :: s, e, convH (update h' l (value v)) ⟩.
  = {unfold convH; rewrite <- hmap_update}
    ⟨c, VAL (convV v) :: s, e, update (convH h') l (value' (convV v)) ⟩.
  <== {apply vm_write}
    ⟨WRITE, VAL (convV v) :: THU l c e :: s, e', convH h'⟩.
  <<= {apply IHeval}
    ⟨comp' x WRITE, THU l c e :: s, e', convH h⟩.
  <== {eapply vm_lookup_thunk}
    ⟨LOOKUP i c, s, e, convH h ⟩.
  [].

  assert (deref (convH h) l = Some (value' (convV v)))
    by (unfold convH; rewrite hmap_deref; rewrite H0; reflexivity).
  begin
    ⟨c, VAL (convV v) :: s, e, convH h ⟩.
  <== {eapply vm_lookup_value }
    ⟨LOOKUP i c, s, e, convH h ⟩.
  [].


  begin
    ⟨c, VAL (Fun' (comp' x RET) e) :: s, e, convH h ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp' x RET) c, s, e, convH h ⟩.
  [].
  

  
  assert (alloc (convH h') (convHE (thunk y e)) = (convH h'', l)).
  unfold convH. eapply hmap_alloc in H0. apply H0.
  
  begin
    ⟨c, VAL (convV x'') :: s, e, convH h''' ⟩.
  <== { apply vm_ret }
    ⟨RET, VAL (convV x'') :: FUN c e :: s, l :: e', convH h''' ⟩.
  <<= { apply IHeval2 }
    ⟨comp' x' RET, FUN c e :: s, l :: e', convH h'' ⟩.
  <== {apply vm_app}
    ⟨APP (comp' y WRITE) c, VAL (Fun' (comp' x' RET) e') :: s, e, convH h'⟩.
   = {reflexivity}
    ⟨APP (comp' y WRITE) c, VAL (convV (Fun x' e')) :: s, e, convH h'⟩.
  <<= { apply IHeval1 }
    ⟨comp' x (APP (comp' y WRITE) c), s, e, convH h⟩.
  [].
Qed.
    

Ltac inv := match goal with
              | [H1 : nth ?e ?i = Some ?l1,
                 H2 : nth ?e ?i = Some ?l2 |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | [H1 : deref ?h ?l = Some ?v1,
                 H2 : deref ?h ?l = Some ?v2 |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | [H1 : alloc ?h ?l = _,
                 H2 : alloc ?h ?l = _ |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | _ => idtac
            end.

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; repeat inv; try reflexivity.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r h, p ⇓[nil,empty,h] r.

Theorem sound p s C : terminates p -> ⟨comp p, s, nil, empty⟩ =>>! C -> 
                          exists r h, C = ⟨HALT , VAL (convV r) :: s, nil, convH h⟩ 
                                    /\ p ⇓[nil, empty, h] r.
Proof.
  unfold terminates. intros. destruct H as [r T]. destruct T as [h T].
  
  pose (spec p nil r HALT s) as H'. exists r. exists h. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. pose (H' empty h) as H. unfold convH in H. 
  rewrite hmap_empty in H. apply H. assumption. intro Con. destruct Con. 
  inversion H. assumption.
Qed.
