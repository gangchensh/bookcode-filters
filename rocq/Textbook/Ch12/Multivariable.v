From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.
Module Ch12.

(* BEGIN definition *)
Definition size2 (h : R * R) : R :=
  Rmax (Rabs (fst h)) (Rabs (snd h)).

Definition Linear2 (L : R * R -> R) : Prop :=
  (forall h k, L (fst h + fst k, snd h + snd k) = L h + L k) /\
  (forall t h, L (t * fst h, t * snd h) = t * L h).

Definition HasTotalDerivative2 (f : R * R -> R)
    (a : R * R) (L : R * R -> R) : Prop :=
  Linear2 L /\
  forall eps : R, 0 < eps -> exists delta : R,
    0 < delta /\ forall h : R * R, size2 h < delta ->
    Rabs (f (fst a + fst h, snd a + snd h) - f a - L h)
      <= eps * size2 h.                           (* 同时控制全部小向量增量 *)
(* END definition *)

Lemma size2_bounds (h : R * R) :
  0 <= size2 h /\ Rabs (fst h) <= size2 h /\
  Rabs (snd h) <= size2 h.
Proof.
  unfold size2. split.
  - eapply Rle_trans; [apply Rabs_pos | apply Rmax_l].
  - split; [apply Rmax_l | apply Rmax_r].
Qed.

(* BEGIN product *)
Theorem product_remainder (a h : R * R) :
  (fst a + fst h) * (snd a + snd h) - fst a * snd a -
    (snd a * fst h + fst a * snd h) = fst h * snd h.
Proof. ring. Qed.                                (* 展开后只剩二阶交叉项 *)

Theorem product_derivative (a : R * R) :
  HasTotalDerivative2 (fun x => fst x * snd x) a
    (fun h => snd a * fst h + fst a * snd h).
Proof.
  split.
  - split; intros; cbn; ring.                     (* 候选映射保持加法和标量乘法 *)
  - intros eps Heps. exists eps. split; [exact Heps |].
  intros h Hsmall. cbn [fst snd].
  rewrite product_remainder, Rabs_mult.            (* 目标化为|h₁||h₂|≤eps·size2 h *)
  destruct (size2_bounds h) as [Hr [Hx Hy]].
  pose proof (Rabs_pos (fst h)).
  pose proof (Rabs_pos (snd h)). nra.              (* |h₁||h₂|≤size2(h)²<eps·size2(h) *)
Qed.
(* END product *)

(* BEGIN native_product *)
Theorem product_native (a : R * R) :
  filterdiff (fun x : R * R => fst x * snd x) (locally a)
    (fun h => fst h * snd a + fst a * snd h).
Proof.
  apply (@filterdiff_mult R_AbsRing (locally a) _ a).
  - intros P HP. exact HP.                        (* 源滤子就是中心a的邻域滤子 *)
  - intros x y. apply Rmult_comm.                 (* 实数乘法可交换 *)
Qed.
(* END native_product *)

(* BEGIN linear *)
Theorem linear_filterdiff (c d : R) (a : R * R) :
  filterdiff (fun x : R * R => c * fst x + d * snd x)
    (locally a) (fun h => c * fst h + d * snd h).
Proof.
  apply filterdiff_linear.                        (* 线性函数的微分就是自身 *)
  split.
  - intros x y. cbn. ring.                        (* 保持向量加法 *)
  - intros k x. cbn. ring.                        (* 保持实数标量乘法 *)
  - exists (Rabs c + Rabs d + 1).
    split; [pose proof (Rabs_pos c); pose proof (Rabs_pos d); lra |].
    intros [x y].
    change (Rabs (c * x + d * y) <=
      (Rabs c + Rabs d + 1) * norm (x,y)).
    eapply Rle_trans; [apply Rabs_triang |].
    rewrite !Rabs_mult.
    pose proof (@norm_prod R_AbsRing R_NormedModule R_NormedModule x y) as Hnorm.
    change (Rmax (Rabs x) (Rabs y) <= norm (x,y) <=
      sqrt 2 * Rmax (Rabs x) (Rabs y)) in Hnorm.
    pose proof (Rmax_l (Rabs x) (Rabs y)).
    pose proof (Rmax_r (Rabs x) (Rabs y)).
    pose proof (Rabs_pos c). pose proof (Rabs_pos d).
    pose proof (Rabs_pos x). nra.                  (* 以常数乘输入范数控制输出 *)
Qed.
(* END linear *)

(* BEGIN jacobian *)
Theorem chain_coefficients (c d a b h k : R) :
  c * (2*a*h+k) + d * (b*h+a*k) =
    (2*c*a+d*b)*h + (c+d*a)*k.
Proof. ring. Qed.                                (* 行向量乘2×2雅可比矩阵 *)
(* END jacobian *)

(* BEGIN native_chain *)
Theorem scaled_product_native (c : R) (a : R * R) :
  filterdiff (fun x : R * R => c * (fst x * snd x)) (locally a)
    (fun h => c * (fst h * snd a + fst a * snd h)).
Proof.
  apply (filterdiff_comp
    (fun x : R * R => fst x * snd x) (fun t : R => c*t)
    (fun h => fst h * snd a + fst a * snd h) (fun t : R => c*t)).
  - apply product_native.                        (* 内层在a处的二元乘积微分 *)
  - exact (@filterdiff_scal_r R_AbsRing R_NormedModule
      (filtermap (fun x : R*R => fst x*snd x) (locally a)) _ c Rmult_comm).
                                                  (* 外层沿内层推送的源取微分 *)
Qed.
(* END native_chain *)

(* BEGIN outer_expansion *)
Theorem outer_square_expansion (h k : R) :
  1+(3+(2*h+k)+h^2)^2+(2+(2*h+k)+h*k)^2-14 =
  10*(2*h+k)+(6*h^2+4*h*k+2*(2*h+k)^2+
    2*(2*h+k)*(h^2+h*k)+h^4+h^2*k^2).
Proof. ring. Qed.                                (* 分离一次项与二阶以上余项 *)
(* END outer_expansion *)
End Ch12.
