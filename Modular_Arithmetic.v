From Coq Require Import Natural.Peano.NPeano.
From Coq Require Import ZArith.

Open Scope Z_scope.

Lemma mod_mult_or: forall a b c: Z, 
  (a | b) \/ (a | c) -> (a | (b * c)).
Proof.
  intros. destruct H.
  - destruct H as [x y]. subst. unfold Z.divide.
    exists (x * c). Admitted.