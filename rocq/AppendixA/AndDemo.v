Example and_demo : True /\ True.                        (* 合并两个恒真命题 *)
Proof.
  split.
  - exact I.
  - exact I.
Qed.
