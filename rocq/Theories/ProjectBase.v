Definition above (cutoff n : nat) : Prop := cutoff <= n.

Lemma above_self : forall n : nat, above n n.           (* 每个自然数都不小于自身 *)
Proof.
  intro n. unfold above. exact (le_n n).
Qed.
