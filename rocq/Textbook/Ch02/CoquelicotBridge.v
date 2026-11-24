From Textbook.Ch02 Require Import Eventually.
Require Import Coquelicot.Coquelicot.

Theorem EventuallyNat_iff_Coquelicot (P : nat -> Prop) :  (* 本书最终成立等价于Coquelicot自然数版本 *)
  EventuallyNat P <-> eventually P.
Proof.
  unfold EventuallyNat, eventually.
  reflexivity.                                          (* 两边展开定义后相同 *)
Qed.
