Require Import List.

Fixpoint nth {A} (l:list A) (i:nat) : option A :=
  match l with
    | nil => None
    | x :: xs => match i with
                   | 0 => Some x
                   | S j => nth xs j
                 end
  end.

Lemma nth_map A B l i (f : A -> B) : nth (map f l) i = option_map f (nth l i).
Proof.
  intros.
  generalize dependent i.
  induction l; intros; simpl. reflexivity.

  destruct i; simpl;auto.
Qed.
