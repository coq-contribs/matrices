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


Require Export carrier.
Require Export vectors.

 
Module Type TVectors.
Parameter A : Set.
Parameter Aopp : A -> A.
Parameters (Aplus Aminus Amult: A -> A -> A).
Parameters (A0 : A) (A1 : A).
Parameter A_ring : ring_theory A0 A1 Aplus Amult Aminus Aopp (eq(A:=A)).

Parameter mkvect : forall (x : A) (n : nat), vect A n.
Parameter addvect : forall n : nat, vect A n -> vect A n -> vect A n.
Parameter scalprod : forall n : nat, vect A n -> vect A n -> A.
Parameter oppvect : forall n : nat, vect A n -> vect A n.
Parameter multscal : forall (a : A) (n : nat), vect A n -> vect A n.

Parameter mkrowI : forall n i : nat, 0 <= i -> i <= n -> vect A n.

Axiom
  addvect_sym :
    forall (n : nat) (w w' : vect A n), addvect n w w' = addvect n w' w.

Axiom
  addvect_assoc :
    forall (n : nat) (v w x : vect A n),
    addvect n v (addvect n w x) = addvect n (addvect n v w) x.

Axiom
  addvect_zero_l :
    forall (n : nat) (w : vect A n), addvect n (mkvect A0 n) w = w.

Axiom
  addvect_reg :
    forall (n : nat) (v1 v2 w1 w2 : vect A n),
    v1 = v2 -> w1 = w2 -> addvect n v1 w1 = addvect n v2 w2.

Axiom
  addvect_oppvect :
    forall (n : nat) (a : vect A n), addvect n a (oppvect n a) = mkvect A0 n.

Axiom
  scalprod_reg :
    forall (n : nat) (v w v' w' : vect A n),
    v = v' -> w = w' -> scalprod n v w = scalprod n v' w'.
Axiom
  scalprod_sym :
    forall (n : nat) (v w : vect A n), scalprod n v w = scalprod n w v.
Axiom
  scalprod_zero_l :
    forall (n : nat) (w : vect A n), scalprod n (mkvect A0 n) w = A0.

Axiom
  scalprod_distr_l :
    forall (n : nat) (a b w : vect A n),
    scalprod n (addvect n a b) w = Aplus (scalprod n a w) (scalprod n b w).

Axiom
  scalprod_distr_r :
    forall (n : nat) (a b w : vect A n),
    scalprod n w (addvect n a b) = Aplus (scalprod n w a) (scalprod n w b).

Axiom
  scalprod_multscal :
    forall (a : A) (n : nat) (v w : vect A n),
    scalprod n (multscal a n v) w = Amult a (scalprod n v w).

Axiom
  mkrowI_nth :
    forall (n : nat) (w : vect A n) (i : nat) (H1 : 0 <= i) 
      (H1' : 0 < i) (H2 H2' : i <= n),
    scalprod n (mkrowI n i H1 H2) w = nth A i n w H1' H2'.

Axiom
  nth_multscal :
    forall (i n : nat) (v : vect A n) (a : A) (h3 : 0 < i) (h4 : i <= n),
    nth A i n (multscal a n v) h3 h4 = Amult a (nth A i n v h3 h4).

Axiom
  nth_addvect :
    forall (i n : nat) (v w : vect A n) (h1 : 0 < i) (h2 : i <= n),
    nth A i n (addvect n v w) h1 h2 =
    Aplus (nth A i n v h1 h2) (nth A i n w h1 h2).

End TVectors.

Module Vectors (C: Carrier) <: TVectors with Definition A := C.A with
  Definition Aopp := C.Aopp with Definition Aplus := C.Aplus with
  Definition Amult := C.Amult with Definition Aminus := C.Aminus with
  Definition A0 := C.A0 with Definition A1 := C.A1 with
  Definition A_ring := C.A_ring.

Definition A := C.A.
Definition Aopp := C.Aopp.
Definition Aplus := C.Aplus.
Definition Amult := C.Amult.
Definition Aminus := C.Aminus.
Definition A0 := C.A0.
Definition A1 := C.A1.
Definition A_ring := C.A_ring.

Import C.
Add Ring Ar : A_ring.

(* functions *)

Fixpoint mkvect (x : A) (n : nat) {struct n} : vect A n :=
  match n as w return (vect A w) with
  | O => vnil A
  | S p => vcons A p x (mkvect x p)
  end.

Definition eq_add_S_tr (n m : nat) (H : S n = S m) : n = m := f_equal pred H.


Fixpoint addvect (n : nat) (v : vect A n) {struct v} :
 vect A n -> vect A n :=
  match v in (vect _ k) return (vect A k -> vect A k) with
  | vnil => fun v' => vnil A
  | vcons n1 x1 v1 =>
      fun v' : vect A (S n1) =>
      match v' in (vect _ k) return (k = S n1 -> vect A k) with
      | vnil => fun h => vnil A
      | vcons n2 x2 v2 =>
          fun h =>
          vcons A n2 (Aplus x1 x2)
            (addvect n2
               (eq_rec n1 (fun n : nat => vect A n) v1 n2
                  (eq_add_S_tr n1 n2 (sym_eq h))) v2)
      end (refl_equal (S n1))
  end.

Fixpoint scalprod (n : nat) (v : vect A n) {struct v} : 
 vect A n -> A :=
  match v in (vect _ k) return (vect A k -> A) with
  | vnil => fun v' => A0
  | vcons n1 x1 v1 =>
      fun v' : vect A (S n1) =>
      match v' in (vect _ k) return (k = S n1 -> A) with
      | vnil => fun h => A0
      | vcons n2 x2 v2 =>
          fun h =>
          Aplus (Amult x1 x2)
            (scalprod n2
               (eq_rec n1 (fun n : nat => vect A n) v1 n2
                  (eq_add_S_tr n1 n2 (sym_eq h))) v2)
      end (refl_equal (S n1))
  end.

Fixpoint oppvect (n : nat) (v : vect A n) {struct v} : 
 vect A n :=
  match v in (vect _ w) return (vect A w) with
  | vnil => vnil A
  | vcons p v vs => vcons A p (Aopp v) (oppvect p vs)
  end.
 
Fixpoint multscal (a : A) (n : nat) (v : vect A n) {struct v} : 
 vect A n :=
  match v in (vect _ w) return (vect A w) with
  | vnil => vnil A
  | vcons p v vs => vcons A p (Amult a v) (multscal a p vs)
  end.

Lemma o1 : forall i : nat, 0 <= i -> 0 <= pred i.
intros; omega.
Qed.
 
Lemma o2 : forall i n0 : nat, i <= S n0 -> pred i <= n0.
intros; omega.
Qed.
 
 
Definition mkrowI : forall n i : nat, 0 <= i -> i <= n -> vect A n.
fix 1.
intros n; case n.
intros i Hi1 Hi2; exact (vnil A).
intros n0 i Hi1 Hi2.
apply vcons.
case (eq_nat_dec i 1).
intros; exact A1.
intros; exact A0.
apply mkrowI with (i := pred i).
apply o1; assumption.
apply o2; assumption.
Defined.

(* lemmas *)

Lemma addvect_sym :
 forall (n : nat) (w w' : vect A n), addvect n w w' = addvect n w' w.
intros n w w'.
eapply
 (induc2 A
    (fun (n : nat) (w w' : vect A n) => addvect n w w' = addvect n w' w))
 .
simpl in |- *; trivial.
intros n0 v v' HR a b.
simpl in |- *.
cut (Aplus a b = Aplus b a); [ intros Hcut; rewrite Hcut | ring ].
rewrite HR.
trivial.
Qed.

Lemma addvect_assoc :
 forall (n : nat) (v w x : vect A n),
 addvect n v (addvect n w x) = addvect n (addvect n v w) x.
intros n v w x.
eapply
 (induc3 A
    (fun (n : nat) (v w x : vect A n) =>
     addvect n v (addvect n w x) = addvect n (addvect n v w) x))
 .
simpl in |- *; trivial.
intros n0 v0 w0 x0 HR a b c.
simpl in |- *.
rewrite HR.
cut (Aplus a (Aplus b c) = Aplus (Aplus a b) c).
intros Hrew; rewrite Hrew.
trivial.
ring.
Qed.

Lemma addvect_zero_l :
 forall (n : nat) (w : vect A n), addvect n (mkvect A0 n) w = w.
intros n w.
eapply
 (induc1 A (fun (n : nat) (w : vect A n) => addvect n (mkvect A0 n) w = w))
 .
simpl in |- *; trivial.
intros n0 v0 HR a.
simpl in |- *.
cut (Aplus A0 a = a); [ intros Hrew; rewrite Hrew | ring ].
rewrite HR.
trivial.
Qed.

Lemma addvect_reg :
 forall (n : nat) (v1 v2 w1 w2 : vect A n),
 v1 = v2 -> w1 = w2 -> addvect n v1 w1 = addvect n v2 w2.
intros n v1 v2 w1 w2 h1 h2; rewrite h1; rewrite h2; trivial.
Qed.

Lemma addvect_oppvect :
 forall (n : nat) (a : vect A n), addvect n a (oppvect n a) = mkvect A0 n.
intros n a.
eapply
 (induc1 A
    (fun (n : nat) (a : vect A n) => addvect n a (oppvect n a) = mkvect A0 n))
 .
simpl in |- *; trivial.
intros n0 v HR a0; simpl in |- *.
rewrite HR.
cut (Aplus a0 (Aopp a0) = A0); [ intros Hcut; rewrite Hcut | ring ].
trivial.
Qed.

Lemma scalprod_reg :
 forall (n : nat) (v w v' w' : vect A n),
 v = v' -> w = w' -> scalprod n v w = scalprod n v' w'.
intros n v w v' w' h1 h2; rewrite h1; rewrite h2; trivial.
Qed.
 
Lemma scalprod_sym :
 forall (n : nat) (v w : vect A n), scalprod n v w = scalprod n w v.
intros n v w.
eapply
 (induc2 A
    (fun (n : nat) (v w : vect A n) => scalprod n v w = scalprod n w v))
 .
simpl in |- *; trivial.
intros n0 v0 v' H a b; try assumption.
simpl in |- *.
rewrite H.
ring.
Qed.

Lemma scalprod_zero_l :
 forall (n : nat) (w : vect A n), scalprod n (mkvect A0 n) w = A0.
intros n w.
eapply
 (induc1 A (fun (n : nat) (w : vect A n) => scalprod n (mkvect A0 n) w = A0))
 .
simpl in |- *; trivial.
intros n0 w0 HR.
simpl in |- *; rewrite HR.
intros; ring.
Qed.

Lemma scalprod_distr_l :
 forall (n : nat) (a b w : vect A n),
 scalprod n (addvect n a b) w = Aplus (scalprod n a w) (scalprod n b w).
intros n a b w.
eapply
 (induc3 A
    (fun (n : nat) (a b w : vect A n) =>
     scalprod n (addvect n a b) w = Aplus (scalprod n a w) (scalprod n b w)))
 .
simpl in |- *; ring.
intros n0 v v' v'' HR a0 b0 c; try assumption.
simpl in |- *.
rewrite HR.
ring.
Qed.

Lemma scalprod_distr_r :
 forall (n : nat) (a b w : vect A n),
 scalprod n w (addvect n a b) = Aplus (scalprod n w a) (scalprod n w b).
intros n a b w.
eapply
 (induc3 A
    (fun (n : nat) (a b w : vect A n) =>
     scalprod n w (addvect n a b) = Aplus (scalprod n w a) (scalprod n w b)))
 .
symmetry  in |- *; simpl in |- *; ring.
intros n0 v v' v'' H a0 b0 c; try assumption.
simpl in |- *.
rewrite H.
ring.
Qed.
 
Lemma scalprod_multscal :
 forall (a : A) (n : nat) (v w : vect A n),
 scalprod n (multscal a n v) w = Amult a (scalprod n v w).
intros a n v w.
eapply
 (induc2 A
    (fun (n : nat) (v w : vect A n) =>
     scalprod n (multscal a n v) w = Amult a (scalprod n v w)))
 .
simpl in |- *; trivial.
ring.
intros n0 v0 v' H a0 b; try assumption.
simpl in |- *.
rewrite H.
ring.
Qed. 
 
Lemma mkrowI_mkvect :
 forall (n : nat) (H1 : 0 <= 0) (H2 : 0 <= n), mkrowI n 0 H1 H2 = mkvect A0 n.
intros n; elim n.
simpl in |- *; trivial.
intros n0 HR; simpl in |- *.
intros; rewrite HR.
trivial.
Qed.
 
Lemma ring_thm2 : forall x y : A, Aplus (Amult A0 x) y = y.
intros; ring.
Qed.
 
Lemma lt_decompose :
 forall i' : nat, 0 < i' -> i' = 1 \/ (exists i'' : nat, i' = S (S i'')).
intros i'; case i'.
intros H; inversion H.
intros j; case j.
left; trivial.
intros n Hn; right; exists n; trivial.
Qed.
 
Lemma mkrowI_nth :
 forall (n : nat) (w : vect A n) (i : nat) (H1 : 0 <= i) 
   (H1' : 0 < i) (H2 H2' : i <= n),
 scalprod n (mkrowI n i H1 H2) w = nth A i n w H1' H2'.
intros n w; elim w.
intros i; case i.
intros H1 H1'; inversion H1'.
intros i' H1 H1' H2 H2'.
cut False; [ intros Hfalse; elim Hfalse | omega ].
intros n0 a v HR i' H1 H1' H2 H2'.
simpl in |- *.
elim (lt_decompose _ H1').
intros Hi'; generalize H1 H1' H2 H2' HR; clear H1 H1' H2 H2' HR.
rewrite Hi'.
intros H1 H1' H2 H2' HR.
simpl in |- *.
rewrite (mkrowI_mkvect n0).
rewrite scalprod_zero_l.
ring.
intros Hex; elim Hex; intros x Hx.
generalize H1 H1' H2 H2' HR; clear H1 H1' H2 H2' HR.
rewrite Hx.
intros H1 H1' H2 H2' HR.
cbv beta iota delta -[nth scalprod mkrowI] in |- *.
rewrite
 (HR (S x) (o1 (S (S x)) H1) (lt_O_Sn x) (o2 (S (S x)) n0 H2)
    (le_Sn_le_n_pred (S x) (S n0) H2')).
simpl in |- *.
rewrite ring_thm2.
trivial.
Qed.

Lemma head_multscal :
 forall (n : nat) (v : vect A n) (a : A) (h : 0 < n),
 head A n (multscal a n v) h = Amult a (head A n v h).
intros n v; elim v.
intros a h; inversion h.
intros n0 a v0 H a0 h; try assumption.
simpl in |- *; trivial.
Qed.
 
Lemma tail_multscal :
 forall (n : nat) (v : vect A n) (a : A),
 tail A n (multscal a n v) = multscal a (pred n) (tail A n v).
intros n v; elim v.
simpl in |- *; trivial.
intros n0 a v0 H a0; try assumption.
simpl in |- *; trivial.
Qed.
 
Lemma nth_multscal :
 forall (i n : nat) (v : vect A n) (a : A) (h3 : 0 < i) (h4 : i <= n),
 nth A i n (multscal a n v) h3 h4 = Amult a (nth A i n v h3 h4).
intros i; elim i using two_step_ind.
intros n v a h3; inversion h3.
intros n v a h3 h4; try assumption.
simpl in |- *.
rewrite head_multscal.
trivial.
intros n H n0 v a h3 h4; try assumption.
simpl in |- *.
case (zerop n).
simpl in |- *; rewrite tail_multscal.
rewrite head_multscal.
trivial.
intros H'.
do 2 rewrite tail_multscal.
rewrite H.
trivial.
Qed.

Lemma head_addvect :
 forall (n : nat) (a b : vect A n) (h : 0 < n),
 head A n (addvect n a b) h = Aplus (head A n a h) (head A n b h).
intros n a b.
eapply
 (induc2 A
    (fun (n : nat) (a b : vect A n) =>
     forall h : 0 < n,
     head A n (addvect n a b) h = Aplus (head A n a h) (head A n b h)))
 .
intros h; inversion h.
intros n0 v v' H a0 b0 h; try assumption.
simpl in |- *; trivial.
Qed.
 
Lemma tail_addvect :
 forall (n : nat) (a b : vect A n),
 tail A n (addvect n a b) = addvect (pred n) (tail A n a) (tail A n b).
intros n a b.
eapply
 (induc2 A
    (fun (n : nat) (a b : vect A n) =>
     tail A n (addvect n a b) = addvect (pred n) (tail A n a) (tail A n b)))
 .
simpl in |- *; trivial.
intros n0 v v' H a0 b0; try assumption.
simpl in |- *; trivial.
Qed.
 
Lemma nth_addvect :
 forall (i n : nat) (v w : vect A n) (h1 : 0 < i) (h2 : i <= n),
 nth A i n (addvect n v w) h1 h2 =
 Aplus (nth A i n v h1 h2) (nth A i n w h1 h2).
intros i; elim i using two_step_ind.
intros n v w h1; inversion h1.
intros n v w h1 h2; try assumption.
simpl in |- *.
rewrite head_addvect.
trivial.
intros n H n0 v w h1 h2; try assumption.
simpl in |- *.
case (zerop n).
rewrite tail_addvect.
rewrite head_addvect; trivial.
intros H'.
do 2 rewrite tail_addvect.
rewrite
 (H (pred (pred n0)) (tail A (pred n0) (tail A n0 v))
    (tail A (pred n0) (tail A n0 w)) H'
    (le_Sn_le_n_pred n (pred n0) (le_Sn_le_n_pred (S n) n0 h2)))
 .
trivial.
Qed.

End Vectors.

(* 
                Local Variables: 
                mode: coq 
                coq-prog-name: "/usr/local/coq-7.4/bin/coqtop -emacs -q"
                compile-command: "make vectors.vo"
                End:*)
