From Stdlib Require Import Sets.Ensembles Arith Lia.
From Textbook.Ch02 Require Import Eventually.

Definition Above100 : Ensemble nat :=
  fun n => 100 <= n.

Local Notation "'A100'" := Above100.                    (* 声明本节使用的数学记号 *)
Local Notation "x 'inN' A" := (In nat A x)              (* 声明本节使用的数学记号 *)
  (at level 70, no associativity).

Example member_with_notation : 105 inN A100.            (* 用自定义记号验证105属于A100 *)
Proof.
  change (100 <= 105).
  lia.                                                  (* 核对自然数或整数算术 *)
Qed.

Declare Scope chapter_sets_scope.                       (* 声明本章集合记号的作用域 *)
Delimit Scope chapter_sets_scope with chsets.           (* 指定显式选择该作用域的后缀 *)
Local Notation "x ∈ A" := (In nat A x)                  (* 声明本节使用的数学记号 *)
  (at level 70, no associativity) : chapter_sets_scope.
Local Infix "∩" := (Intersection nat)                   (* 把交集记号对应到 Intersection *)
  (at level 40, left associativity) : chapter_sets_scope.
Local Notation "{ x | P }" := (fun x : nat => P)        (* 声明本节使用的数学记号 *)
  (at level 0, x at level 99) : chapter_sets_scope.

Example notation_inter (A B : Ensemble nat) (n : nat) :  (* 交集成员记号等价于两个成员命题的合取 *)
  (n ∈ (A ∩ B))%chsets <-> In nat A n /\ In nat B n.
Proof.
  split.
  - intro H.
    destruct H as [x HA HB].
    split; assumption.
  - intros [HA HB].
    apply Intersection_intro; assumption.
Qed.

Example notation_builder :                              (* 集合构造记号与成员谓词等价 *)
  ({ n | 100 <= n })%chsets = Above100.
Proof.
  reflexivity.                                          (* 两边展开定义后相同 *)
Qed.

Example member_above100 : In nat Above100 105.          (* 105属于大于等于100的集合 *)
Proof.
  change (100 <= 105).
  lia.                                                  (* 核对自然数或整数算术 *)
Qed.

Example not_member_above100 : ~ In nat Above100 99.     (* 99不属于大于等于100的集合 *)
Proof.
  change (~ (100 <= 99)).
  lia.                                                  (* 核对自然数或整数算术 *)
Qed.

Example tail_subset : Included nat (Tail 1000) (Tail 100).  (* 从1000开始的尾集包含于从100开始的尾集 *)
Proof.
  intros n Hn.
  change (100 <= n).
  change (1000 <= n) in Hn.
  lia.                                                  (* 核对自然数或整数算术 *)
Qed.

Theorem set_inter_comm (A B : Ensemble nat) :           (* 证明集合交的交换律 *)
  Same_set nat (Intersection nat A B) (Intersection nat B A).  (* 陈述交集交换律 *)
Proof.
  split.
  - intros n Hn.
    destruct Hn as [x HA HB].
    apply Intersection_intro.
    + exact HB.
    + exact HA.
  - intros n Hn.
    destruct Hn as [x HB HA].
    apply Intersection_intro.
    + exact HA.
    + exact HB.
Qed.

Definition TailSets : Ensemble (Ensemble nat) :=
  fun A => exists N : nat, Included nat (Tail N) A.

Theorem TailSets_iff (A : Ensemble nat) :               (* 尾集集合族成员等价于包含尾集 *)
  In (Ensemble nat) TailSets A <-> EventuallyNat A.
Proof.
  unfold In, TailSets, Included, Tail, EventuallyNat.
  reflexivity.                                          (* 两边展开定义后相同 *)
Qed.
