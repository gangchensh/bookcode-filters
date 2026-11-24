From Stdlib Require Import Reals Lra Psatz.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
From Textbook.Ch03 Require Import LimitRules.
From Textbook.Ch05 Require Import Sequences.

Module Ch04Local.
Import Ch02 Ch03 Ch03Approach.
Open Scope R_scope.

Definition domain_filter (a : R) (S : R -> Prop) : BookFilter R :=
  near_within a (fun x => S x /\ x <> a).             (* 定义域内趋近，并排除中心点 *)

Definition DomainLimit (f : R -> R) (S : R -> Prop) (a b : R) : Prop :=
  Approaches f (domain_filter a S) (neighborhood_filter b).

Definition IsAccumulationPoint (S : R -> Prop) (a : R) : Prop :=
  forall delta : R, 0 < delta ->
    exists x : R, Rabs (x-a) < delta /\ S x /\ x <> a.

Theorem domain_limit_iff (f : R -> R) (S : R -> Prop) (a b : R) :
  DomainLimit f S a b <-> forall eps : R, 0 < eps ->
  exists delta : R, 0 < delta /\ forall x : R,
    Rabs (x-a) < delta -> (S x /\ x <> a) -> Rabs (f x-b) < eps.
Proof. unfold DomainLimit. rewrite real_iff. reflexivity. Qed.

Theorem domain_proper (S : R -> Prop) (a : R) :
  IsAccumulationPoint S a -> IsProper (domain_filter a S).
Proof.
  intros Hacc [delta [Hdelta Hempty]].
  destruct (Hacc delta Hdelta) as [x [Hx [HS Hne]]].
  exact (Hempty x Hx (conj HS Hne)).                 (* 聚点提供的点排除空成员 *)
Qed.

Theorem domain_limit_congr (f g : R -> R) (S : R -> Prop) (a b : R) :
  Eventually (domain_filter a S) (fun x => f x = g x) ->
  DomainLimit f S a b -> DomainLimit g S a b.
Proof.
  intros Heq Hf.
  exact (Ch03Rules.approaches_congr f g _ _ Heq Hf).  (* 复用同一源上的最终相等替换 *)
Qed.

Theorem limit_eventually_nonzero {X : Type} (f : X -> R) (F : BookFilter X) (b : R) :
  Approaches f F (neighborhood_filter b) -> b <> 0 ->
  Eventually F (fun x => f x <> 0).
Proof.
  intros Hf Hb.
  assert (Hpos : 0 < Rabs b) by (apply Rabs_pos_lt; exact Hb).
  pose proof ((proj1 (real_iff _ _ _)) Hf (Rabs b/2)) as Hnear.
  assert (Heps : 0 < Rabs b/2) by lra. specialize (Hnear Heps).
  eapply upward; [exact Hnear |].
  intros x Hx Hzero.
  change (Rabs (f x-b) < Rabs b/2) in Hx.
  rewrite Hzero in Hx.
  replace (0-b) with (-b) in Hx by ring.
  rewrite Rabs_Ropp in Hx. lra.                      (* 若为零，到极限的距离就是|b| *)
Qed.

Theorem sequence_into_domain (x : nat -> R) (S : R -> Prop) (a : R) :
  Ch05.Converges x a -> (forall n : nat, S (x n) /\ x n <> a) ->
  Approaches x tail_filter (domain_filter a S).
Proof.
  intros Hx HS V [delta [Hdelta HV]].
  destruct ((proj1 (Ch05.converges_iff x a)) Hx delta Hdelta) as [N HN].
  exists N. intros n Hn.
  exact (HV (x n) (HN n Hn) (HS n)).                 (* 距离、定义域和去心条件同时满足 *)
Qed.

Theorem domain_limit_sequence (f : R -> R) (S : R -> Prop) (a b : R) (x : nat -> R) :
  DomainLimit f S a b -> Ch05.Converges x a ->
  (forall n : nat, S (x n) /\ x n <> a) ->
  Ch05.Converges (fun n => f (x n)) b.
Proof.
  intros Hf Hx HS.
  exact (Ch03Rules.approaches_comp x f _ _ _
    (sequence_into_domain x S a Hx HS) Hf).          (* 中间源滤子已包含全部限制条件 *)
Qed.

Theorem lift_domain {X : Type} (f : X -> R) (F : BookFilter X) (T : R -> Prop) (b : R) :
  Approaches f F (neighborhood_filter b) ->
  Eventually F (fun x => T (f x) /\ f x <> b) ->
  Approaches f F (domain_filter b T).
Proof.
  intros Hf HT V [delta [Hdelta HV]].
  eapply upward.
  - eapply meets; [exact ((proj1 (real_iff _ _ _)) Hf delta Hdelta) | exact HT].
  - intros x [Hx Hdom]. exact (HV (f x) Hx Hdom).     (* 将距离界与中间定义域要求合并 *)
Qed.

Theorem compose_domain {X : Type} (f : X -> R) (g : R -> R)
    (F : BookFilter X) (T : R -> Prop) (b c : R) :
  Approaches f F (neighborhood_filter b) ->
  Eventually F (fun x => T (f x) /\ f x <> b) ->
  DomainLimit g T b c -> Approaches (fun x => g (f x)) F (neighborhood_filter c).
Proof.
  intros Hf HT Hg.
  exact (Ch03Rules.approaches_comp f g _ _ _ (lift_domain f F T b Hf HT) Hg).
Qed.

End Ch04Local.
