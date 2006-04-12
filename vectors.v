(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export Eqdep.
(* The lemma uniq is taken from Bruno Barras , see coq-club msg # Fri, 17 May 2002 17:17:49 +0200 
   It does not require any axiom because equality over nat is decidable *)
Require Export Eqdep_dec.
(* required for vcons *)
Require Export Peano_dec.
Require Export Omega.
 
Axiom proof_irr : forall (A : Prop) (p q : A), p = q.
 
Lemma two_step_ind :
 forall P : nat -> Prop,
 P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) -> forall n : nat, P n.
intros P h0 h1 hr n; cut (P n /\ P (S n)).
intros H; elim H; trivial.
elim n.
split; trivial.
intros n0 H; try assumption.
elim H.
intros H0 H1; try assumption.
split; [ trivial | apply hr; trivial ].
Qed.
 
Section vect_def.
Variable A : Set.
 
Inductive vect : nat -> Set :=
  | vnil : vect 0
  | vcons : forall n : nat, A -> vect n -> vect (S n).
 
Lemma uniq : forall v : vect 0, v = vnil.
intros v.
change (v = eq_rec _ vect vnil _ (refl_equal 0)) in |- *.
generalize (refl_equal 0).
change
  ((fun (n : nat) (v : vect n) =>
    forall e : 0 = n, v = eq_rec _ vect vnil _ e) 0 v) 
 in |- *.
case v; intros.
apply K_dec_set with (p := e).
exact eq_nat_dec.
reflexivity.
discriminate e.
Qed.
(* These two following theorems are derived from the hardware contrib of Coq *)
 
Definition eq_vect := eq_dep nat vect.
 
Lemma decompose_dep :
 forall n m : nat,
 m = S n ->
 forall v : vect (S n),
 {a : A &  {v' : vect n | eq_vect (S n) v (S n) (vcons n a v')}}.
intros n m H v.
generalize H; clear H.
dependent inversion_clear v
 with
  (fun (n' : nat) (vl : vect n') =>
   m = n' -> {a : A &  {v' : vect n | eq_vect n' vl (S n) (vcons n a v')}}).
unfold eq_vect in |- *.
intros H; exists a; exists v0.
apply eq_dep_intro.
Qed.
 
Lemma decompose :
 forall (n : nat) (v : vect (S n)),
 {a : A &  {v' : vect n | v = vcons n a v'}}.
intros n v.
cut {a : A &  {t : vect n | eq_vect (S n) v (S n) (vcons n a t)}}.
intros H; elim H; clear H.
intros a H; elim H; clear H.
intros v' H.
exists a; exists v'.
apply eq_dep_eq with (U := nat) (P := vect) (p := S n).
unfold eq_vect in H; trivial.
apply (decompose_dep n (S n)); trivial.
Qed.
(* end of hardware contrib *)
 
Lemma eq_vect_vcons :
 forall (c n : nat) (vc : vect c) (vn : vect n) (a a' : A),
 a = a' ->
 eq_vect c vc n vn -> eq_vect (S c) (vcons c a vc) (S n) (vcons n a' vn).
intros c n vc vn a a' H H'.
rewrite H.
cut (eq_vect (S c) (vcons c a' vc) (S c) (vcons c a' vc)).
intros Hcut.
unfold eq_vect in |- *.
apply
 (eq_dep_ind nat vect c vc
    (fun (n0 : nat) (v0 : vect n0) =>
     eq_dep nat vect (S c) (vcons c a' vc) (S n0) (vcons n0 a' v0)) Hcut n vn
    H').
unfold eq_vect in |- *; apply eq_dep_intro.
Qed.
 
Lemma vcons_lemma :
 forall (n : nat) (x y : A) (xs ys : vect n),
 x = y -> xs = ys -> vcons n x xs = vcons n y ys.
intros n x y xs ys Hxy Hxsys.
rewrite Hxy.
rewrite Hxsys.
trivial.
Qed.
(* recursion principles *)
 
Lemma induc1 :
 forall P : forall n : nat, vect n -> Prop,
 P 0 vnil ->
 (forall (n : nat) (v : vect n), P n v -> forall a : A, P (S n) (vcons n a v)) ->
 forall (n : nat) (v : vect n), P n v.
intros P Hnil Hvcons n.
elim n.
intros v.
replace v with vnil; [ idtac | rewrite uniq; auto ].
exact Hnil.
intros n0 HR v.
elim (decompose n0 v).
intros ve Hve; elim Hve; intros xe Heq.
rewrite Heq.
apply Hvcons.
apply HR.
Qed.
 
Lemma induc2 :
 forall P : forall n : nat, vect n -> vect n -> Prop,
 P 0 vnil vnil ->
 (forall (n : nat) (v v' : vect n),
  P n v v' -> forall a b : A, P (S n) (vcons n a v) (vcons n b v')) ->
 forall (n : nat) (v v' : vect n), P n v v'.
intros P Hnil Hvcons n.
elim n.
intros v v'.
replace v with vnil; [ idtac | rewrite uniq; auto ].
replace v' with vnil; [ idtac | rewrite uniq; auto ].
exact Hnil.
intros n0 HR v v'.
elim (decompose n0 v).
intros ve Hve; elim Hve; intros xe Heq.
rewrite Heq.
elim (decompose n0 v').
intros ve' Hve'; elim Hve'; intros xe' Heq'.
rewrite Heq'.
apply Hvcons.
apply HR.
Qed.
 
Lemma induc3 :
 forall P : forall n : nat, vect n -> vect n -> vect n -> Prop,
 P 0 vnil vnil vnil ->
 (forall (n : nat) (v v' v'' : vect n),
  P n v v' v'' ->
  forall a b c : A, P (S n) (vcons n a v) (vcons n b v') (vcons n c v'')) ->
 forall (n : nat) (v v' v'' : vect n), P n v v' v''.
intros P Hvnil Hvcons n.
elim n.
intros v v' v''.
replace v with vnil; [ idtac | rewrite uniq; auto ].
replace v' with vnil; [ idtac | rewrite uniq; auto ].
replace v'' with vnil; [ idtac | rewrite uniq; auto ].
exact Hvnil.
intros n0 HR v v' v''.
elim (decompose n0 v).
intros ve Hve; elim Hve; intros xe Heq.
rewrite Heq.
elim (decompose n0 v').
intros ve' Hve'; elim Hve'; intros xe' Heq'.
rewrite Heq'.
elim (decompose n0 v'').
intros ve'' Hve''; elim Hve''; intros xe'' Heq''.
rewrite Heq''.
apply Hvcons.
apply HR.
Qed.
(* some basic operations on vectors *)
 
Definition head (n : nat) (v : vect n) :=
  match v in (vect n) return (0 < n -> A) with
  | vnil => fun h : 0 < 0 => False_rec A (lt_irrefl 0 h)
  | vcons p a v' => fun h : 0 < S p => a
  end.
 
Lemma head_lemma_1 :
 forall v v' : vect 1, v = v' -> head 1 v (le_n 1) = head 1 v' (le_n 1).
intros v v' H; rewrite H; trivial.
Qed.
 
Definition tail (n : nat) (v : vect n) :=
  match v in (vect m) return (vect (pred m)) with
  | vnil => vnil
  | vcons p a v' => v'
  end.
 
Lemma le_S_lt_O : forall n m : nat, S m <= n -> 0 < n.
intros; apply lt_le_trans with (S m); auto with arith.
Qed.
 
Lemma lt_le_pred : forall n m : nat, n < m -> n <= pred m.
simple induction n; simple induction m; auto with arith.
Qed.
 
Lemma le_Sn_le_n_pred : forall n m : nat, S n <= m -> n <= pred m.
intros; apply lt_le_pred; trivial.
Qed.
 
Theorem zerop : forall n : nat, {n = 0} + {0 < n}.
destruct n; auto with arith.
Defined.
 
Fixpoint nth (i : nat) : forall n : nat, vect n -> 0 < i -> i <= n -> A :=
  fun (n : nat) (v : vect n) =>
  match i as j return (0 < j -> j <= n -> A) with
  | O => fun (h' : 0 < 0) h'' => False_rec A (lt_irrefl 0 h')
  | S p =>
      fun (h' : 0 < S p) (h'' : S p <= n) =>
      match zerop p with
      | left _ => head n v (le_S_lt_O _ _ h'')
      | right h => nth p (pred n) (tail n v) h (le_Sn_le_n_pred _ _ h'')
      end
  end.
 
Remark nth_lemma_aux : forall (i n : nat) (Hi2 : S i <= S n), i <= n.
intros; apply le_S_n; trivial.
Qed.
 
Lemma nth_lemma :
 forall (i n : nat) (a : A) (v : vect n) (Hi1 : 0 < S (S i))
   (Hi2 : S (S i) <= S n) (Hi1' : 0 < S i),
 nth (S (S i)) (S n) (vcons n a v) Hi1 Hi2 =
 nth (S i) n v Hi1' (le_Sn_le_n_pred (S i) (S n) Hi2).
intros i; elim i using two_step_ind.
intros n a v Hi1 Hi2 Hi1'; simpl in |- *; trivial.
intros i' a v Hi1 Hi2 Hi1'; simpl in |- *; trivial.
intros i' HR n' a v Hi1 Hi2 Hi1'; simpl in |- *; trivial.
Qed.
 
Lemma nth_lemma' :
 forall (c n : nat) (w : vect n) (a : A) (H1 : 0 < S c) 
   (H2 : S c <= S n) (H1' : 0 < c),
 nth (S c) (S n) (vcons n a w) H1 H2 =
 nth c n w H1' (le_Sn_le_n_pred c (S n) H2).
intros c; elim c.
intros n w a H1 H2 H1'; inversion H1'.
intros c' HR.
simpl in |- *; trivial.
Qed.
(* last *)
 
Lemma last_o1 : forall n c' : nat, S c' <= n -> 0 < n - c'.
intros; omega.
Qed.
 
Lemma last_o2 : forall n c' : nat, n - c' <= n.
intros; omega.
Qed.
 
Lemma last_o3 : forall c' : nat, 0 <= c'.
intros; omega.
Qed.
 
Lemma last_o4 : forall c' n : nat, S c' <= n -> c' <= n.
intros; omega.
Qed.
 
Definition last :
  forall (n : nat) (v : vect n) (c : nat), 0 <= c -> c <= n -> vect c.
intros n v; fix 1.
intros c; case c.
intros; apply vnil.
intros c' Hc1' Hc2'.
apply vcons.
apply (nth (n - c') n v).
apply last_o1; assumption.
apply last_o2; assumption.
apply last.
apply last_o3; assumption.
apply last_o4; assumption.
Defined.
 
Lemma last_vcons :
 forall (n : nat) (w : vect n) (c : nat) (H1 : 0 < n - c) 
   (H2 : n - c <= n) (H1c' : 0 <= S c) (H2c' : S c <= n) 
   (H1c : 0 <= c) (H2c : c <= n),
 vcons c (nth (n - c) n w H1 H2) (last n w c H1c H2c) =
 last n w (S c) H1c' H2c'.
intros n w c H1 H2 H1c' H2c' H1c H2c.
unfold last at 2 in |- *.
apply vcons_lemma.
rewrite (proof_irr _ H1 (last_o1 n c H2c')).
rewrite (proof_irr _ H2 (last_o2 n c)).
trivial.
rewrite (proof_irr _ H1c (last_o3 c)).
rewrite (proof_irr _ H2c (last_o4 c n H2c')).
trivial.
Qed.
 
Lemma last_S :
 forall (c n : nat) (a : A) (v : vect n) (H1 : 0 <= c) 
   (H2 : c <= n) (H2' : c <= S n),
 last n v c H1 H2 = last (S n) (vcons n a v) c H1 H2'.
intros c; elim c.
intros n a v H1 H2 H2'; try assumption.
rewrite (uniq (last n v 0 H1 H2)).
rewrite (uniq (last (S n) (vcons n a v) 0 H1 H2')); trivial.
intros c' HR.
intros n a v H1 H2 H2'.
unfold last in |- *.
apply vcons_lemma.
generalize (last_o1 (S n) c' H2') (last_o2 (S n) c').
rewrite <- minus_Sn_m.
intros Hcut1 Hcut2.
symmetry  in |- *.
rewrite (nth_lemma' (n - c') n v a Hcut1 Hcut2 (last_o1 n c' H2)).
rewrite (proof_irr _ (le_Sn_le_n_pred (n - c') (S n) Hcut2) (last_o2 n c')).
trivial.
replace
 (fix last (c0 : nat) : 0 <= c0 -> c0 <= n -> vect c0 :=
    match c0 as c1 return (0 <= c1 -> c1 <= n -> vect c1) with
    | O => fun (_ : 0 <= 0) (_ : 0 <= n) => vnil
    | S c'0 =>
        fun (_ : 0 <= S c'0) (Hc2' : S c'0 <= n) =>
        vcons c'0 (nth (n - c'0) n v (last_o1 n c'0 Hc2') (last_o2 n c'0))
          (last c'0 (last_o3 c'0) (last_o4 c'0 n Hc2'))
    end) with (last n v); [ idtac | trivial ].
replace
 (fix last (c0 : nat) : 0 <= c0 -> c0 <= S n -> vect c0 :=
    match c0 as c1 return (0 <= c1 -> c1 <= S n -> vect c1) with
    | O => fun (_ : 0 <= 0) (_ : 0 <= S n) => vnil
    | S c'0 =>
        fun (_ : 0 <= S c'0) (Hc2' : S c'0 <= S n) =>
        vcons c'0
          (nth (S n - c'0) (S n) (vcons n a v) (last_o1 (S n) c'0 Hc2')
             (last_o2 (S n) c'0))
          (last c'0 (last_o3 c'0) (last_o4 c'0 (S n) Hc2'))
    end) with (last (S n) (vcons n a v)); [ idtac | trivial ].
omega.
apply (HR n a v (last_o3 c') (last_o4 c' n H2) (last_o4 c' (S n) H2')).
Qed.
 
Lemma last_vcons' :
 forall (n : nat) (w : vect n) (c : nat) (a : A) (H1 : 0 < n - c)
   (H2 : n - c <= n) (H1c' : 0 <= S c) (H2c' : S c <= S n) 
   (H1c : 0 <= c) (H2c : c <= n),
 vcons c (nth (n - c) n w H1 H2) (last n w c H1c H2c) =
 last (S n) (vcons n a w) (S c) H1c' H2c'.
intros n; elim n.
intros w c a H1 H2 H1c' H2c' H1c H2c; cut (c = 0).
intros Hrew; generalize w a H1 H2 H1c' H2c' H1c H2c;
 clear w a H1 H2 H1c' H2c' H1c H2c.
rewrite Hrew.
intros w a H1; simpl in H1; inversion H1.
omega.
intros n0 HR v c.
intros a H1 H2 H1c' H2c' H1c H2c.
cut (c <= n0).
intros Hcut; generalize a H1 H2 H1c' H2c' H1c H2c;
 clear a H1 H2 H1c' H2c' H1c H2c.
rewrite <- (minus_Sn_m _ _ Hcut).
2: omega.
intros a H1 H2 H1c' H2c' H1c H2c.
unfold last at 2 in |- *.
apply vcons_lemma.
generalize (last_o1 (S (S n0)) c H2c') (last_o2 (S (S n0)) c).
replace (S (S n0) - c) with (S (S (n0 - c))); [ idtac | omega ].
intros Hcut1 Hcut2.
symmetry  in |- *.
rewrite (nth_lemma' (S (n0 - c)) (S n0) v a Hcut1 Hcut2 H1).
rewrite (proof_irr _ H2 (le_Sn_le_n_pred (S (n0 - c)) (S (S n0)) Hcut2)).
trivial.
replace
 (fix last (c : nat) : 0 <= c -> c <= S (S n0) -> vect c :=
    match c as c1 return (0 <= c1 -> c1 <= S (S n0) -> vect c1) with
    | O => fun (_ : 0 <= 0) (_ : 0 <= S (S n0)) => vnil
    | S c' =>
        fun (_ : 0 <= S c') (Hc2' : S c' <= S (S n0)) =>
        vcons c'
          (nth (S (S n0) - c') (S (S n0)) (vcons (S n0) a v)
             (last_o1 (S (S n0)) c' Hc2') (last_o2 (S (S n0)) c'))
          (last c' (last_o3 c') (last_o4 c' (S (S n0)) Hc2'))
    end) with (last (S (S n0)) (vcons (S n0) a v)); 
 [ idtac | trivial ].
generalize (last_S c (S n0) a v H1c H2c (last_o4 c (S (S n0)) H2c')).
rewrite (proof_irr _ H1c (last_o3 c)).
trivial.
Qed.
 
Lemma last_n :
 forall (c n : nat) (v : vect n) (H : c = n) (H1 : 0 <= c) (H2 : c <= n),
 eq_vect c (last n v c H1 H2) n v.
intros c; elim c.
intros n v H; simpl in |- *.
intros H1 H2.
generalize H v; case n.
intros; rewrite uniq.
unfold eq_vect in |- *; apply eq_dep_intro.
intros n' Hd; discriminate Hd.
intros c' HR n; case n.
intros v Hd; discriminate Hd.
intros n' v' Heq H1 H2.
cut (0 < S n' - c'); [ intros Hcut1 | omega ].
cut (S n' - c' <= S n'); [ intros Hcut2 | omega ].
cut (0 <= S c'); [ intros Hcut3 | omega ].
cut (S c' <= S n'); [ intros Hcut4 | omega ].
cut (0 <= c'); [ intros Hcut5 | omega ].
cut (c' <= S n'); [ intros Hcut6 | omega ].
elim (decompose _ v').
intros x0 Hx; elim Hx; clear Hx; intros v0 Heq'.
rewrite Heq'.
rewrite <-
 (last_vcons (S n') (vcons n' x0 v0) c' Hcut1 Hcut2 H1 H2 Hcut5 Hcut6)
 .
apply
 (eq_vect_vcons c' n' (last (S n') (vcons n' x0 v0) c' Hcut5 Hcut6) v0
    (nth (S n' - c') (S n') (vcons n' x0 v0) Hcut1 Hcut2) x0).
cut (S n' - c' = 1); [ intros Hcut'' | omega ].
generalize Hcut1 Hcut2; rewrite Hcut''.
simpl in |- *; trivial.
rewrite <- (last_S c' n' x0 v0 Hcut5 (le_S_n _ _ Hcut4) Hcut6).
apply HR.
omega.
Qed.
 
Lemma last_n' :
 forall (n : nat) (v : vect n) (H1 : 0 <= n) (H2 : n <= n),
 last n v n H1 H2 = v.
intros; apply (eq_dep_eq nat vect n (last n v n H1 H2) v).
apply last_n.
trivial.
Qed.
 
End vect_def.
 
Fixpoint map (A B : Set) (f : A -> B) (n : nat) (v : vect A n) {struct v} :
 vect B n :=
  match v in (vect _ p) return (vect B p) with
  | vnil => vnil B
  | vcons p x v' => vcons B p (f x) (map A B f p v')
  end.
 
Lemma map_2 :
 forall (A B : Set) (n : nat) (t : vect A n) (f : A -> B) 
   (g : B -> A) (H : forall x : A, g (f x) = x),
 map B A g n (map A B f n t) = map A A (fun x : A => g (f x)) n t.
intros A2 B n; elim n.
intros t f g H; rewrite (uniq A2).
rewrite (uniq B (map A2 B f 0 t)).
simpl in |- *; trivial.
intros n0 H t f g H0; try assumption.
elim (decompose A2 n0 t).
intros x Hx; elim Hx; intros v Hvx; rewrite Hvx; clear Hx Hvx.
simpl in |- *.
rewrite H.
trivial.
apply H0.
Qed.
 
Lemma map_2' :
 forall (A B : Set) (n : nat) (t : vect A n) (f : A -> B) 
   (g : B -> A) (H : forall x : A, g (f x) = x),
 map B A g n (map A B f n t) = t.
intros A2 B n; elim n.
intros t f g H; rewrite (uniq A2).
rewrite (uniq B (map A2 B f 0 t)).
simpl in |- *; trivial.
intros n0 H t f g H0; try assumption.
elim (decompose A2 n0 t).
intros x Hx; elim Hx; intros v Hvx; rewrite Hvx; clear Hx Hvx.
simpl in |- *.
rewrite H.
rewrite H0; trivial.
apply H0.
Qed.

  (* 
  Local Variables: 
  mode: coq 
  coq-prog-name: "/usr/local/coq-7.4/bin/coqtop -emacs -q"
  compile-command: "make vectors.vo"
  End:
  *)