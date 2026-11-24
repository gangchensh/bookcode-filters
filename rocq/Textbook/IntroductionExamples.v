From Stdlib Require Import ZArith.
Open Scope Z_scope.

Example one_div_zero : 1 / 0 = 0.                       (* 库中的实数1除以0定义为0 *)
Proof. reflexivity. Qed.                                (* 展开定义后两边相同 *)

Example integer_div_zero : forall a : Z, a / 0 = 0.     (* 库中的整数除以0定义为0 *)
Proof. intro a. apply Z.div_0_r. Qed.
