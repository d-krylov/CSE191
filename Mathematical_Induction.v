From Coq Require Import Arith.
From Coq Require Import ZArith.
From Coq Require Import Lia.

Open Scope nat_scope.


Fixpoint sum_n n :=
  match n with
  | 0 => 0
  | S p => p + sum_n p
end.

Lemma sum_n_p: forall n, 
  2 * sum_n n + n = n * n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. lia.
Qed.

Fixpoint sum_odd_n (n: nat): nat :=
  match n with
  | 0 => 0
  | S p => 1 + 2 * p + sum_odd_n p
end.

Lemma odd_sum: forall n: nat, 
  sum_odd_n n = n * n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. apply f_equal. rewrite Nat.add_0_r.
    rewrite Nat.mul_succ_r. rewrite <- Nat.add_comm with (n) (n * n).
    rewrite Nat.add_assoc. reflexivity.
Qed.

Fixpoint sum_n3 (n: nat): nat :=
  match n with
  | 0 => 0
  | S p => p * p * p + sum_n3 p
end.

Lemma sum_cube_p : forall n: nat, 
  sum_n3 n = (sum_n n) * (sum_n n).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. Admitted.

Fixpoint fibonacci (n: nat): Z :=
  match n with
  | O => 1
  | S O => 1
  | S (S n as p) => fibonacci p + fibonacci n
end.

Theorem cassini_identity: forall (n: nat),
  fibonacci (n + 1) * fibonacci (n - 1) - (fibonacci n) ^ 2 = Zpower_nat (-1) n.
Proof.
  intros. induction n.
  - simpl.