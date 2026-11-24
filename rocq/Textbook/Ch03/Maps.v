From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
Import Ch02 Ch03 Ch03Approach.

(* BEGIN image *)
Definition image_filter {X Y : Type} (f : X -> Y)
    (F : BookFilter X) : BookFilter Y.
Proof.
  refine {| members := fun V => members F (preimage f V) |}.
  - exact (whole F).
  - intros A B HA HB. exact (meets F _ _ HA HB).
  - intros A B HA HAB.
    eapply upward; [exact HA |]. intros x Hx. exact (HAB _ Hx).
Defined.
(* END image *)

(* BEGIN order *)
Definition Finer {X : Type} (F G : BookFilter X) : Prop :=
  forall A, members G A -> members F A.

Theorem approaches_image_iff {X Y : Type} (f : X -> Y)
    (F : BookFilter X) (G : BookFilter Y) :
  Approaches f F G <-> Finer (image_filter f F) G.
Proof. reflexivity. Qed.
(* END order *)

(* BEGIN generated *)
Definition generated_filter {I X : Type} (B : I -> X -> Prop)
    (HI : exists i : I, True)
    (HB : forall i j, exists k, forall x, B k x -> B i x /\ B j x)
    : BookFilter X.
Proof.
  refine {| members := fun U => exists i, forall x, B i x -> U x |}.
  - destruct HI as [i _]. exists i. intros x Hx. constructor.
  - intros U V [i Hi] [j Hj].
    destruct (HB i j) as [k Hk].                   (* 找同时细化两个范围的B k *)
    exists k. intros x Hx. destruct (Hk x Hx) as [H1 H2].
    split; [exact (Hi x H1) | exact (Hj x H2)].
  - intros U V [i Hi] HUV. exists i.
    intros x Hx. exact (HUV x (Hi x Hx)).
Defined.
(* END generated *)
