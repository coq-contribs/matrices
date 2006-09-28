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


Require Export operators.

Module Type TMatrices.

Parameter A : Set.
Parameter Aopp : A -> A.
Parameters (Aplus Amult Aminus : A -> A -> A).
Parameters (A0 : A) (A1 : A).
Parameter A_ring : ring_theory A0 A1 Aplus Amult Aminus Aopp (eq(A:=A)).

Parameter Lmatrix : nat -> nat -> Set.
Parameter
  addmatrix : forall n m : nat, Lmatrix n m -> Lmatrix n m -> Lmatrix n m.
Parameter
  prodmat : forall n m p : nat, Lmatrix m n -> Lmatrix p m -> Lmatrix p n.
Parameter oppmatrix : forall n m : nat, Lmatrix n m -> Lmatrix n m.
Parameter o : forall n m : nat, Lmatrix n m.
Parameter I : forall n : nat, Lmatrix n n.

Axiom
  addmatrix_sym :
    forall (n m : nat) (w w' : Lmatrix n m),
    addmatrix n m w w' = addmatrix n m w' w.

Axiom
  addmatrix_assoc :
    forall (n m : nat) (w w' w'' : Lmatrix n m),
    addmatrix n m (addmatrix n m w w') w'' =
    addmatrix n m w (addmatrix n m w' w'').

Axiom
  addmatrix_oppmatrix :
    forall (n m : nat) (w : Lmatrix n m),
    addmatrix n m w (oppmatrix n m w) = o n m.

Axiom
  addmatrix_zero_l :
    forall (n m : nat) (w : Lmatrix n m), addmatrix n m (o n m) w = w.

Axiom I_mat : forall (m n : nat) (w : Lmatrix n m), prodmat m m n (I m) w = w.
Axiom mat_I : forall (m n : nat) (w : Lmatrix n m), prodmat m n n w (I n) = w.

Axiom
  prodmat_distr_l :
    forall (n m p : nat) (a b : Lmatrix m n) (w : Lmatrix p m),
    prodmat n m p (addmatrix m n a b) w =
    addmatrix p n (prodmat n m p a w) (prodmat n m p b w).

Axiom
  prodmat_distr_r :
    forall (n m p : nat) (a b : Lmatrix p m) (w : Lmatrix m n),
    prodmat n m p w (addmatrix p m a b) =
    addmatrix p n (prodmat n m p w a) (prodmat n m p w b).

Axiom
  prodmat_assoc :
    forall (n m p q : nat) (a : Lmatrix m n) (b : Lmatrix p m)
      (c : Lmatrix q p),
    prodmat n p q (prodmat n m p a b) c = prodmat n m q a (prodmat m p q b c).

End TMatrices.

Module Matrices (C: Carrier) <: TMatrices with Definition A := C.A with
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

Module MyVectors := Vectors C.
Import MyVectors.
Import C.

(* definitions *)
Definition Lmatrix (n m : nat) := vect (vect A n) m.
(* defined by rows : (Lmatrix A n m) have m rows and n columns
   the aim is to show the ring structure of n,n matrix *)

Definition eq_add_S_tr (n m : nat) (H : S n = S m) : n = m := f_equal pred H.

Fixpoint addmatrix (n m : nat) (v : Lmatrix n m) {struct v} :
 Lmatrix n m -> Lmatrix n m :=
  match v in (vect _ k) return (Lmatrix n k -> Lmatrix n k) with
  | vnil => fun v' => vnil (vect A n)
  | vcons m1 x1 v1 =>
      fun v' : Lmatrix n (S m1) =>
      match v' in (vect _ k) return (k = S m1 -> Lmatrix n k) with
      | vnil => fun h => vnil (vect A n)
      | vcons m2 x2 v2 =>
          fun h =>
          vcons (vect A n) m2 (addvect n x1 x2)
            (addmatrix n m2
               (eq_rec m1 (fun m : nat => Lmatrix n m) v1 m2
                  (eq_add_S_tr m1 m2 (sym_eq h))) v2)
      end (refl_equal (S m1))
  end.

Definition getline (n m : nat) (v : Lmatrix n m) (i : nat) 
  (h : 0 < i) (h' : i <= m) : vect A n := nth (vect A n) i m v h h'.
 
Lemma getline_lemma :
 forall (m : nat) (w : Lmatrix 0 m) (i : nat) (H1 : 0 < i) (H2 : i <= m),
 getline 0 m w i H1 H2 = vnil A.
intros m w i H1 H2.
rewrite (uniq A (getline 0 m w i H1 H2)); trivial.
Qed.
 
Definition getcolumn (n m : nat) (v : Lmatrix n m) 
  (i : nat) (h : 0 < i) (h' : i <= n) : vect A m :=
  map (vect A n) A (fun w : vect A n => nth A i n w h h') m v.
 
Lemma access_sym :
 forall (n m : nat) (w : Lmatrix n m) (i j : nat) (Hj1 : 0 < j)
   (Hj2 : j <= n) (Hi1 : 0 < i) (Hi2 : i <= m),
 nth A i m (getcolumn n m w j Hj1 Hj2) Hi1 Hi2 =
 nth A j n (getline n m w i Hi1 Hi2) Hj1 Hj2.
intros n m.
unfold getline, getcolumn in |- *.
intros w; elim w.
simpl in |- *.
intros i; elim i using two_step_ind.
intros j Hj1 Hj2 Hi1; inversion Hi1.
simpl in |- *.
intros j; elim j using two_step_ind.
intros Hj1; inversion Hj1.
intros Hj1 Hj2 Hi1 Hi2; inversion Hi2.
intros n0 Hj1 Hj2 Hi1 Hi2 Hi3; inversion Hi3.
intros i' HR j; elim j using two_step_ind.
intros Hj1; inversion Hj1.
intros Hh1 Hj2 Hi1 Hi2; inversion Hi2.
intros n0 Hj1 Hj2 Hi1 Hi2 Hi3; inversion Hi3.
intros n' a w' HR.
simpl in |- *.
intros i; elim i using two_step_ind.
intros j Hj1 Hj2 Hi1; inversion Hi1.
simpl in |- *; trivial.
intros i' HR' j Hj1 Hj2 Hi1 Hi2.
cut (0 < S i').
intros Hcut.
rewrite
 (nth_lemma A i' n' (nth A j n a Hj1 Hj2)
    (map (vect A n) A (fun w0 : vect A n => nth A j n w0 Hj1 Hj2) n' w') Hi1
    Hi2 Hcut).
rewrite (HR (S i')).
rewrite (nth_lemma (vect A n) i' n' a w' Hi1 Hi2 Hcut).
trivial.
omega.
Qed.

Lemma o1 : forall (m d : nat) (Hle : S d <= m), 0 < S m - S d.
exact last_o1.
Defined.
 
Lemma o2 : forall m d : nat, S m - S d <= m.
exact last_o2.
Defined.
 
Lemma o3 : forall d : nat, 0 <= d.
exact last_o3.
Defined.
 
Lemma o4 : forall (m d : nat) (Hle : S d <= m), d <= m.
exact (fun m d H => last_o4 d m H).
Defined.
 
Definition prodvectmatrix :
  forall (n m : nat) (v : vect A n) (w : Lmatrix m n) (c : nat),
  0 <= c -> c <= m -> vect A c.
intros n m v w.
fix 1.
intros c; case c.
intros H H'; apply vnil.
intros d Hlt Hle.
apply vcons.
apply (scalprod n v).
eapply (getcolumn m n w) with (i := S m - S d).
apply o1; assumption.
apply o2; assumption.
apply prodvectmatrix.
apply o3; assumption.
apply o4; assumption.
Defined.
 
Definition prodvectmat :
  forall (n m : nat) (v : vect A n) (w : Lmatrix m n), vect A m.
intros n m v w.
apply (prodvectmatrix n m v w m).
apply le_O_n.
apply le_n.
Defined.
 
Fixpoint prodmat (n m p : nat) (w1 : Lmatrix m n) {struct w1} :
 Lmatrix p m -> Lmatrix p n :=
  fun w2 : Lmatrix p m =>
  match w1 in (vect _ a) return (Lmatrix p a) with
  | vnil => vnil (vect A p)
  | vcons n' r1 rs =>
      vcons (vect A p) n' (prodvectmat m p r1 w2) (prodmat n' m p rs w2)
  end.
 
Fixpoint oppmatrix (n m : nat) (w : Lmatrix n m) {struct w} : 
 Lmatrix n m :=
  match w as _ in (vect _ w) return (Lmatrix n w) with
  | vnil => vnil (vect A n)
  | vcons p v vs => vcons (vect A n) p (oppvect n v) (oppmatrix n p vs)
  end.

Fixpoint mkzero (n m : nat) {struct m} : Lmatrix n m :=
  match m as w return (Lmatrix n w) with
  | O => vnil (vect A n)
  | S p => vcons (vect A n) p (mkvect A0 n) (mkzero n p)
  end.
 
Definition o (n m : nat) : Lmatrix n m := mkzero n m.
 
Lemma o1' : forall m0 n : nat, 0 <= n - m0.
intros; omega.
Qed.
 
Lemma o2' : forall m0 n : nat, n - m0 <= n.
intros; apply last_o2; trivial.
Defined.
 
Lemma o3' : forall m0 n : nat, S m0 <= n -> m0 <= n.
exact last_o4.
Defined.
 
Definition I' : forall n m : nat, m <= n -> Lmatrix n m.
intros n; fix 1.
intros m; case m.
intros; apply (vnil (vect A n)).
intros m0 Hm0; unfold Lmatrix in |- *; apply (vcons (vect A n)).
apply mkrowI with (i := n - m0).
apply le_O_n.
apply o2'; assumption.
apply I'.
apply o3'; assumption.
Defined.

Definition I : forall n : nat, Lmatrix n n.
intros n; apply I'.
apply le_n.
Defined.
 
Lemma addmatrix_sym :
 forall (n m : nat) (w w' : Lmatrix n m),
 addmatrix n m w w' = addmatrix n m w' w.
intros n m w w'.
eapply
 (induc2 (vect A n)
    (fun (m : nat) (w w' : Lmatrix n m) =>
     addmatrix n m w w' = addmatrix n m w' w)).
simpl in |- *; trivial.
intros n0 w0 w0' HR w1 w1'.
simpl in |- *.
rewrite HR.
rewrite addvect_sym.
trivial.
Qed.

Lemma addmatrix_assoc :
 forall (n m : nat) (w w' w'' : Lmatrix n m),
 addmatrix n m (addmatrix n m w w') w'' =
 addmatrix n m w (addmatrix n m w' w'').
intros n m w w' w''.
eapply
 (induc3 (vect A n)
    (fun (m : nat) (w w' w'' : Lmatrix n m) =>
     addmatrix n m (addmatrix n m w w') w'' =
     addmatrix n m w (addmatrix n m w' w''))).
simpl in |- *; trivial.
intros n0 v v' v'' HR a b c; simpl in |- *.
rewrite HR.
rewrite addvect_assoc.
trivial.
Qed.

Lemma addmatrix_oppmatrix :
 forall (n m : nat) (w : Lmatrix n m),
 addmatrix n m w (oppmatrix n m w) = o n m.
intros n m w.
eapply
 (induc1 (vect A n)
    (fun (m : nat) (w : Lmatrix n m) =>
     addmatrix n m w (oppmatrix n m w) = o n m)).
simpl in |- *; trivial.
intros n0 v HR a.
simpl in |- *.
rewrite HR.
rewrite addvect_oppvect.
trivial.
Qed.

Lemma addmatrix_zero_l :
 forall (n m : nat) (w : Lmatrix n m), addmatrix n m (o n m) w = w.
intros n m w.
eapply
 (induc1 (vect A n)
    (fun (m : nat) (w : Lmatrix n m) => addmatrix n m (o n m) w = w))
 .
simpl in |- *; trivial.
intros n0 v0 HR a; simpl in |- *.
rewrite HR.
rewrite addvect_zero_l.
trivial.
Qed.

Lemma mkvectA0_prodvectmatrix :
 forall (n m c : nat) (w : Lmatrix m n) (H1 : 0 <= c) (H2 : c <= m),
 prodvectmatrix n m (mkvect A0 n) w c H1 H2 = mkvect A0 c.
intros n m c; generalize n m; clear n m; elim c.
simpl in |- *; trivial.
intros c' HR.
unfold mkvect in |- *; simpl in |- *.
intros n m w H1 H2; apply vcons_lemma.
rewrite scalprod_zero_l; trivial.
rewrite HR; trivial.
Qed.
 
Lemma mkvectA0_prodvectmat :
 forall (n m : nat) (w : Lmatrix m n),
 prodvectmat n m (mkvect A0 n) w = mkvect A0 m.
intros n m w; unfold prodvectmat in |- *; apply mkvectA0_prodvectmatrix.
Qed.
 
Lemma prodvectmatrix_last :
 forall (n m i : nat) (w : Lmatrix n m) (H1 : 0 < i) 
   (H1' : 0 <= i) (H2 : i <= m) (c : nat) (Hc1 : 0 <= c) 
   (Hc2 : c <= n),
 prodvectmatrix m n (mkrowI m i H1' H2) w c Hc1 Hc2 =
 last A n (getline n m w i H1 H2) c Hc1 Hc2.
intros n m i w H1 H1' H2 c; elim c.
intros Hc1 Hc2; simpl in |- *.
trivial.
intros c' HR Hc1' Hc2'.
simpl in |- *.
rewrite HR.
rewrite
 (mkrowI_nth m (getcolumn n m w (n - c') (o1 n c' Hc2') (o2 n c')) i H1' H1
    H2 H2).
rewrite (access_sym n m w i (n - c') (o1 n c' Hc2') (o2 n c') H1 H2).
unfold o1, o2, o3, o4 in |- *; trivial.
Qed.
 
Lemma mkrowI_prodvectmat :
 forall (n m i : nat) (w : Lmatrix m n) (H1 : 0 <= i) 
   (H1' : 0 < i) (H2 : i <= n),
 prodvectmat n m (mkrowI n i H1 H2) w = getline m n w i H1' H2.
intros n m i w H1 H1' H2; try assumption.
rewrite <- (last_n' A m (getline m n w i H1' H2) (le_O_n m) (le_n m)).
unfold prodvectmat in |- *.
apply (prodvectmatrix_last m n i w H1' H1 H2 m (le_O_n m) (le_n m)).
Qed.
 
Lemma I'_simpl :
 forall (n m0 : nat) (H : S m0 <= n) (H2 : n - m0 <= n),
 I' n (S m0) H =
 vcons (vect A n) m0 (mkrowI n (n - m0) (le_O_n (n - m0)) H2)
   (I' n m0 (o3' m0 n H)).
intros n m0 H H2; try assumption.
simpl in |- *; trivial.
rewrite (proof_irr _ (o2' m0 n) H2).
trivial.
Qed.

Lemma I'_mat :
 forall (m n p : nat) (w : Lmatrix p n) (H1 : 0 <= m) (H2 : m <= n),
 prodmat m n p (I' n m H2) w = last (vect A p) n w m H1 H2.
intros m; elim m.
simpl in |- *; trivial.
intros m' HR n p w H1 H2.
rewrite (I'_simpl n m' H2 (last_o2 n m')). 
generalize H1 H2 HR; clear H1 H2 HR; case w.
intros H1 H2 HR; cut False.
intros Hfalse; elim Hfalse.
omega.
intros n0' v' v0' H1 H2 HR.
cbv beta iota delta -[mkrowI scalprod minus nth map prodvectmatrix I' last]
 in |- *.
replace
 (fix prodmat (n0 m0 p0 : nat) (w1 : vect (vect A m0) n0)
              (w2 : vect (vect A p0) m0) {struct w1} : 
  vect (vect A p0) n0 :=
    match w1 in (vect _ n1) return (vect (vect A p0) n1) with
    | vnil => vnil (vect A p0)
    | vcons n' r1 rs =>
        vcons (vect A p0) n'
          (prodvectmatrix m0 p0 r1 w2 p0 (le_O_n p0) (le_n p0))
          (prodmat n' m0 p0 rs w2)
    end) with prodmat; [ idtac | trivial ].
generalize
 (mkrowI_prodvectmat (S n0') p (S n0' - m') (vcons (vect A p) n0' v' v0')
    (le_O_n (S n0' - m')) (last_o1 (S n0') m' H2) (last_o2 (S n0') m')).
unfold prodvectmat in |- *.
intros H; rewrite H; clear H.
simpl in |- *.
apply vcons_lemma.
unfold getline in |- *; simpl in |- *; trivial.
unfold o3' in |- *.
apply
 (HR (S n0') p (vcons (vect A p) n0' v' v0') (last_o3 m')
    (last_o4 m' (S n0') H2)). 
Qed.
 
Lemma I'_mat' :
 forall (n p : nat) (w : Lmatrix p n) (H2 : n <= n),
 prodmat n n p (I' n n H2) w = w.
intros n p w H2; try assumption.
transitivity (last (vect A p) n w n (le_O_n n) H2).
apply I'_mat.
apply (last_n' (vect A p) n w (le_O_n n) H2).
Qed.
 
Lemma I_mat : forall (m n : nat) (w : Lmatrix n m), prodmat m m n (I m) w = w.
intros m n w; try assumption.
unfold I in |- *.
apply I'_mat'.
Qed.

 
Lemma getcolumn_In :
 forall (m' i m : nat) (h : m' <= m) (h1 : 0 <= i) 
   (h2 : i <= m) (h1'' : 0 <= m') (h2'' : m' <= m) 
   (h1' : 0 < i),
 getcolumn m m' (I' m m' h) i h1' h2 =
 last A m (mkrowI m i h1 h2) m' h1'' h2''.
intros m'; elim m'.
unfold getcolumn in |- *; simpl in |- *; trivial.
intros n H i m h h1 h2 h1'' h2'' h1'; try assumption.
unfold getcolumn in |- *; simpl in |- *.
apply vcons_lemma.
rewrite <-
 (mkrowI_nth m (mkrowI m (m - n) (le_O_n (m - n)) (o2' n m)) i h1 h1' h2)
 .
rewrite <-
 (mkrowI_nth m (mkrowI m i h1 h2) (m - n) (le_O_n (m - n)) 
    (last_o1 m n h2'') (last_o2 m n)).
unfold scalprod in |- *.
rewrite scalprod_sym.
unfold o2' in |- *.
trivial.
unfold getcolumn in H.
apply H.
Qed.
 
Lemma mat_I_last_aux :
 forall (i m : nat) (v : vect A m) (h1' : 0 <= i) (h2' : i <= m),
 prodvectmatrix m m v (I m) i h1' h2' = last A m v i h1' h2'.
intros i; elim i.
simpl in |- *; trivial.
intros n H m v h1' h2'; try assumption.
simpl in |- *.
apply vcons_lemma.
cut (0 <= m - n); [ intros Hcuta | omega ].
rewrite <- (mkrowI_nth m v (m - n) Hcuta (last_o1 m n h2') (last_o2 m n)).
rewrite scalprod_sym.
unfold scalprod in |- *.
cut
 (getcolumn m m (I m) (m - n) (o1 m n h2') (o2 m n) =
  mkrowI m (m - n) Hcuta (last_o2 m n)).
intros Hrew'; rewrite Hrew'; trivial.
replace (mkrowI m (m - n) Hcuta (last_o2 m n)) with
 (last A m (mkrowI m (m - n) Hcuta (last_o2 m n)) m (le_O_n m) (le_n m)).
unfold I in |- *; apply getcolumn_In.
apply last_n'.
unfold o3, o4 in |- *; apply H.
Qed.
 
Lemma mat_I_last :
 forall (i n m : nat) (a : Lmatrix m n) (h1 : 0 <= i) (h2 : i <= n),
 prodmat _ _ _ (last (vect A m) n a i h1 h2) (I m) =
 last (vect A m) n a i h1 h2.
intros i; elim i.
simpl in |- *; trivial.
intros n H n0 m a h1 h2; try assumption.
simpl in |- *.
apply (vcons_lemma (vect A m) n).
unfold prodvectmat in |- *.
pattern (nth (vect A m) (n0 - n) n0 a (last_o1 n0 n h2) (last_o2 n0 n)) at 2
 in |- *;
 replace (nth (vect A m) (n0 - n) n0 a (last_o1 n0 n h2) (last_o2 n0 n)) with
  (last A m (nth (vect A m) (n0 - n) n0 a (last_o1 n0 n h2) (last_o2 n0 n)) m
     (le_O_n m) (le_n m)).
apply mat_I_last_aux.
apply last_n'.
apply (H n0 m a (last_o3 n) (last_o4 n n0 h2)).
Qed.
 
Lemma mat_I : forall (m n : nat) (w : Lmatrix n m), prodmat m n n w (I n) = w.
intros m n w; try assumption.
replace w with (last (vect A n) m w m (le_O_n m) (le_n m)).
apply mat_I_last.
apply last_n'.
Qed.

Lemma prodvectmatrix_distr_l :
 forall (n m : nat) (a b : vect A n) (w : Lmatrix m n) 
   (c : nat) (H1 : 0 <= c) (H2 : c <= m),
 prodvectmatrix n m (addvect n a b) w c H1 H2 =
 addvect c (prodvectmatrix n m a w c H1 H2) (prodvectmatrix n m b w c H1 H2).
intros n m a b w c; elim c.
intros H1 H2; simpl in |- *; trivial.
intros n0 HR H1 H2; try assumption.
simpl in |- *.
apply vcons_lemma.
unfold scalprod in |- *.
rewrite scalprod_distr_l.
trivial.
rewrite HR.
trivial.
Qed.
 
Lemma prodvectmat_distr_l :
 forall (n m : nat) (a b : vect A n) (w : Lmatrix m n),
 prodvectmat n m (addvect n a b) w =
 addvect m (prodvectmat n m a w) (prodvectmat n m b w).
intros n m a b w; try assumption.
unfold prodvectmat in |- *.
apply prodvectmatrix_distr_l.
Qed.
 
Lemma prodmat_distr_l :
 forall (n m p : nat) (a b : Lmatrix m n) (w : Lmatrix p m),
 prodmat n m p (addmatrix m n a b) w =
 addmatrix p n (prodmat n m p a w) (prodmat n m p b w).
intros n m p a b w.
eapply
 (induc2 (vect A m)
    (fun (n0 : nat) (a0 b0 : Lmatrix m n0) =>
     prodmat n0 m p (addmatrix m n0 a0 b0) w =
     addmatrix p n0 (prodmat n0 m p a0 w) (prodmat n0 m p b0 w)))
 .
simpl in |- *; trivial.
intros n0 v v' HR a0 b0; try assumption.
simpl in |- *.
apply (vcons_lemma (vect A p) n0).
apply prodvectmat_distr_l.
rewrite HR.
trivial.
Qed.
 
Lemma getcolumn_addvect :
 forall (i p m : nat) (a b : Lmatrix p m) (h1 : 0 < i) (h2 : i <= p),
 getcolumn p m (addmatrix p m a b) i h1 h2 =
 addvect m (getcolumn p m a i h1 h2) (getcolumn p m b i h1 h2).
intros i p m a b; try assumption.
eapply
 (induc2 (vect A p)
    (fun (m : nat) (a b : Lmatrix p m) =>
     forall (h1 : 0 < i) (h2 : i <= p),
     getcolumn p m (addmatrix p m a b) i h1 h2 =
     addvect m (getcolumn p m a i h1 h2) (getcolumn p m b i h1 h2)))
 .
unfold getcolumn in |- *; simpl in |- *; trivial.
intros n v v' H a0 b0 h1 h2; try assumption.
unfold getcolumn in |- *; simpl in |- *.
apply vcons_lemma.
apply nth_addvect.
unfold getcolumn in H.
apply H.
Qed.
 
Lemma prodvectmatrix_distr_r :
 forall (i m p : nat) (a0 : vect A m) (a b : Lmatrix p m) 
   (h1 : 0 <= i) (h2 : i <= p),
 prodvectmatrix m p a0 (addmatrix p m a b) i h1 h2 =
 addvect i (prodvectmatrix m p a0 a i h1 h2)
   (prodvectmatrix m p a0 b i h1 h2).
intros i; elim i.
simpl in |- *; trivial.
intros n H m p a0 a b h1 h2; try assumption.
simpl in |- *.
apply vcons_lemma.
unfold scalprod in |- *.
rewrite <- scalprod_distr_r.
apply scalprod_reg.
trivial.
apply getcolumn_addvect.
apply H.
Qed.
 
Lemma prodmat_distr_r :
 forall (n m p : nat) (a b : Lmatrix p m) (w : Lmatrix m n),
 prodmat n m p w (addmatrix p m a b) =
 addmatrix p n (prodmat n m p w a) (prodmat n m p w b).
intros n m p a b w; try assumption.
eapply
 (induc1 (vect A m)
    (fun (n : nat) (w : Lmatrix m n) =>
     prodmat n m p w (addmatrix p m a b) =
     addmatrix p n (prodmat n m p w a) (prodmat n m p w b)))
 .
simpl in |- *; trivial.
intros n0 v H a0; try assumption.
simpl in |- *.
apply (vcons_lemma (vect A p) n0).
unfold prodvectmat in |- *.
apply prodvectmatrix_distr_r.
apply H.
Qed.
 
 
(* assoc *)
Lemma prodvectmatrix_vnil :
 forall (p n : nat) (h1 : 0 <= p) (h2 : p <= n),
 prodvectmatrix 0 n (vnil A) (vnil (vect A n)) p h1 h2 = mkvect A0 p.
intros p; elim p.
unfold mkvect in |- *; simpl in |- *; trivial.
intros n H n0 h1 h2; try assumption.
unfold mkvect in |- *; simpl in |- *.
apply vcons_lemma.
trivial.
rewrite H; trivial.
Qed.
 
Lemma prodvectmatrix_vcons :
 forall (p' m' p : nat) (x : A) (vx : vect A m') (a : vect A p)
   (v : vect (vect A p) m') (Hp'1 : 0 <= p') (Hp'2 : p' <= p),
 prodvectmatrix (S m') p (vcons A m' x vx) (vcons (vect A p) m' a v) p' Hp'1
   Hp'2 =
 addvect p' (multscal x p' (last A p a p' Hp'1 Hp'2))
   (prodvectmatrix m' p vx v p' Hp'1 Hp'2).
intros p'; elim p'.
simpl in |- *; trivial.
intros n HR m' p x vx a v Hp'1 Hp'2; try assumption.
simpl in |- *.
apply vcons_lemma.
unfold o1, o2 in |- *; unfold getcolumn in |- *; trivial.
unfold o2, o4 in |- *; rewrite HR.
trivial.
Qed.
 
Lemma prodvectmat_vcons :
 forall (m' p : nat) (x : A) (vx : vect A m') (a : vect A p)
   (v : vect (vect A p) m'),
 prodvectmat (S m') p (vcons A m' x vx) (vcons (vect A p) m' a v) =
 addvect p (multscal x p a) (prodvectmat m' p vx v).
intros m' p x vx a v; try assumption.
pattern a at 2 in |- *; replace a with (last A p a p (le_O_n p) (le_n p)).
unfold prodvectmat in |- *.
apply prodvectmatrix_vcons.
apply last_n'.
Qed.
 
Lemma Aplus_Aplus :
 forall a b c d : A, a = b -> c = d -> Aplus a c = Aplus b d.
intros a b c d h h1; rewrite h; rewrite h1; trivial.
Qed.

Lemma nth_mkvect :
 forall (i : nat) (x : A) (n : nat) (hi1 : 0 < i) (hi2 : i <= n),
 nth A i n (mkvect x n) hi1 hi2 = x.
intros i; elim i.
intros x n hi1; inversion hi1.
intros i' HR x n0 hi1 hi2; try assumption.
simpl in |- *.
case (zerop i').
generalize hi2; clear hi2; case n0.
intros hi2; cut False; [ intros Hf; elim Hf | omega ].
simpl in |- *; trivial.
generalize hi2; case n0.
intros hi3 hi4; cut False; [ intros Hf; elim Hf | omega ].
intros n hi0 l; try assumption.
simpl in |- *.
rewrite HR.
trivial.
Qed.

Lemma scalprod_getcolumn_nth :
 forall (p q i : nat) (a0 : vect A p) (b : Lmatrix q p) 
   (h3 : 0 < i) (h4 : i <= q),
 scalprod p a0 (getcolumn q p b i h3 h4) =
 nth A i q (prodvectmat p q a0 b) h3 h4.
intros p q i; try assumption.
intros a0; elim a0.
simpl in |- *.
intros b; rewrite (uniq (vect A q) b).
intros h3 h4; try assumption.
unfold prodvectmat in |- *.
rewrite (prodvectmatrix_vnil q q (le_O_n q) (le_n q)).
rewrite (nth_mkvect i A0 q h3).
trivial.
intros p' a v HR b h3 h4; try assumption.
elim (decompose (vect A q) p' b).
intros v' Hv; elim Hv; intros vs Hvs; rewrite Hvs; clear Hvs.
unfold prodvectmat in |- *.
rewrite (prodvectmatrix_vcons q p' q a v v' vs (le_O_n q) (le_n q)).
simpl in |- *.
unfold prodvectmat in |- *.
rewrite last_n'.
rewrite nth_addvect.
apply Aplus_Aplus.
symmetry  in |- *; apply nth_multscal.
replace (prodvectmatrix p' q v vs q (le_O_n q) (le_n q)) with
 (prodvectmat p' q v vs); [ idtac | trivial ].
unfold getcolumn in HR.
apply (HR vs h3 h4).
Qed.
 
Lemma prodvectmat_scalprod :
 forall (n : nat) (a b : vect A n),
 prodvectmat n 1 a (map A (vect A 1) (fun x : A => vcons A 0 x (vnil A)) n b) =
 vcons A 0 (scalprod n a b) (vnil A).
intros n a b; try assumption.
unfold prodvectmat in |- *; simpl in |- *.
apply vcons_lemma.
unfold getcolumn in |- *; simpl in |- *.
rewrite
 (map_2' A (vect A 1) n b (fun x : A => vcons A 0 x (vnil A))
    (fun w : vect A 1 => head A 1 w (le_S_lt_O 1 0 (o2 1 0)))
    (fun x : A => refl_equal x)).
trivial.
trivial.
Qed.
 
Lemma prodvectmat_scalprod' :
 forall (n : nat) (a b : vect A n),
 head A 1
   (prodvectmat n 1 a
      (map A (vect A 1) (fun x : A => vcons A 0 x (vnil A)) n b)) 
   (le_n 1) = scalprod n a b.
intros n a b; try assumption.
rewrite prodvectmat_scalprod.
simpl in |- *; trivial.
Qed.
 
Lemma prodmat_getcolumn :
 forall (m p q : nat) (a : Lmatrix p m) (b : Lmatrix q p) 
   (i : nat) (h1 : 0 < i) (h2 : i <= q),
 prodmat m p 1 a
   (map A (vect A 1) (fun x : A => vcons A 0 x (vnil A)) p
      (getcolumn q p b i h1 h2)) =
 map A (vect A 1) (fun x : A => vcons A 0 x (vnil A)) m
   (getcolumn q m (prodmat m p q a b) i h1 h2).
intros m p q a; try assumption.
elim a.
simpl in |- *; trivial.
intros n a0 v H b i h1 h2; try assumption.
simpl in |- *.
apply (vcons_lemma (vect A 1) n).
rewrite prodvectmat_scalprod.
apply vcons_lemma.
apply scalprod_getcolumn_nth.
trivial.
rewrite H; trivial.
Qed.
 
Lemma map_prodmat_getcolumn :
 forall (m p q : nat) (v : vect A m) (a : Lmatrix p m) 
   (b : Lmatrix q p) (i : nat) (h1 : 0 < i) (h2 : i <= q),
 scalprod m v
   (map (vect A 1) A (fun x : vect A 1 => head A 1 x (le_n 1)) m
      (prodmat m p 1 a
         (map A (vect A 1) (fun x : A => vcons A 0 x (vnil A)) p
            (getcolumn q p b i h1 h2)))) =
 scalprod m v (getcolumn q m (prodmat m p q a b) i h1 h2).
intros m p q v a b i h1 h2; try assumption.
rewrite prodmat_getcolumn.
rewrite
 (map_2' A (vect A 1) m (getcolumn q m (prodmat m p q a b) i h1 h2)
    (fun x : A => vcons A 0 x (vnil A))
    (fun x : vect A 1 => head A 1 x (le_n 1))).
trivial.
simpl in |- *; trivial.
Qed.

Lemma Amult_scalprod :
 forall (n : nat) (v w : vect A n) (a : A),
 Amult a (scalprod n v w) = scalprod n (multscal a n v) w.
intros n v w a;
 eapply
  (induc2 A
     (fun (n : nat) (v w : vect A n) =>
      Amult a (scalprod n v w) = scalprod n (multscal a n v) w))
  .
simpl in |- *.
ring.
intros n0 v0 v' H a0 b; try assumption.
simpl in |- *.
rewrite <- H.
ring.
Qed.
 
Lemma prodvectmatrix_map :
 forall (i p : nat) (a0 : A) (b1 : vect A p) (c : Lmatrix 1 p) 
   (h1 : 0 <= i) (h2 : i <= 1),
 prodvectmatrix p 1 (multscal a0 p b1) c i h1 h2 =
 multscal a0 i (prodvectmatrix p 1 b1 c i h1 h2).
intros i; elim i.
simpl in |- *; trivial.
intros n H p a0 b1 c h1 h2; try assumption.
simpl in |- *.
apply vcons_lemma.
generalize h1 h2; clear h1 h2; case n.
2: intros n0 h1 h2; inversion h2.
2: inversion H1.
intros h1 h2; try assumption.
unfold getcolumn in |- *; simpl in |- *.
rewrite Amult_scalprod.
trivial.
apply H.
Qed.
 
Lemma prodvectmat_map :
 forall (p : nat) (a0 : A) (b1 : vect A p) (c : Lmatrix 1 p),
 prodvectmat p 1 (multscal a0 p b1) c = multscal a0 1 (prodvectmat p 1 b1 c).
intros p a0 b1 c; try assumption.
unfold prodvectmat in |- *; apply prodvectmatrix_map.
Qed.
 
Lemma prodvectmat_assoc_1 :
 forall (m p : nat) (a : vect A m) (b : Lmatrix p m) (c : Lmatrix 1 p),
 prodvectmat p 1 (prodvectmat m p a b) c =
 prodvectmat _ _ a (prodmat _ _ _ b c).
intros m p a; elim a.
intros b; rewrite (uniq (vect A p) b).
intros c; simpl in |- *.
unfold prodvectmat in |- *; rewrite prodvectmatrix_vnil.
unfold prodvectmat in |- *; rewrite mkvectA0_prodvectmatrix.
rewrite (prodvectmatrix_vnil 1 1 (le_O_n 1) (le_n 1)).
trivial.
intros n a0 v H b c; try assumption.
elim (decompose (vect A p) n b).
intros b1 Hb1; elim Hb1; intros bs Hbs; rewrite Hbs; clear Hb1 Hbs.
simpl in |- *.
rewrite prodvectmat_vcons.
rewrite prodvectmat_vcons.
rewrite prodvectmat_distr_l.
rewrite H.
apply addvect_reg.
apply prodvectmat_map.
trivial.
Qed.
 
Lemma prodvectmatrix_assoc :
 forall (v m p q : nat) (a : vect A m) (b : Lmatrix p m) 
   (c : Lmatrix q p) (h1 : 0 <= v) (h2 : v <= q),
 prodvectmatrix p q (prodvectmatrix m p a b p (le_O_n p) (le_n p)) c v h1 h2 =
 prodvectmatrix m q a (prodmat m p q b c) v h1 h2.
intros v; elim v.
intros m p q a b c h1 h2; try assumption.
simpl in |- *; trivial.
intros n HR m p q a b c h1 h2; try assumption.
simpl in |- *.
apply vcons_lemma.
rewrite <- map_prodmat_getcolumn.
rewrite <-
 (prodvectmat_scalprod' m a
    (map (vect A 1) A (fun x : vect A 1 => head A 1 x (le_n 1)) m
       (prodmat m p 1 b
          (map A (vect A 1) (fun x : A => vcons A 0 x (vnil A)) p
             (getcolumn q p c (q - n) (o1 q n h2) (o2 q n))))))
 .
rewrite <- (prodvectmat_scalprod' p (prodvectmat m p a b)).
apply head_lemma_1.
rewrite (map_2' (vect A 1) A).
rewrite prodvectmat_assoc_1.
trivial.
intros x.
elim (decompose _ 0 x).
intros x1 Hx; elim Hx; intros xs Hxs; rewrite Hxs; clear Hx Hxs.
simpl in |- *; rewrite (uniq A xs); trivial.
apply HR.
Qed.
 
Lemma prodmat_assoc :
 forall (n m p q : nat) (a : Lmatrix m n) (b : Lmatrix p m) (c : Lmatrix q p),
 prodmat n p q (prodmat n m p a b) c = prodmat n m q a (prodmat m p q b c).
intros n m p q a b c; try assumption.
eapply
 (induc1 (vect A m)
    (fun (n0 : nat) (a0 : Lmatrix m n0) =>
     prodmat n0 p q (prodmat n0 m p a0 b) c =
     prodmat n0 m q a0 (prodmat m p q b c))).
simpl in |- *; trivial.
intros n0 v HR a0; try assumption.
simpl in |- *.
apply (vcons_lemma (vect A q) n0).
unfold prodvectmat in |- *; apply prodvectmatrix_assoc.
apply HR.
Qed.

End Matrices.

Module matrixZ := Matrices Zc.


(* 
 Local Variables: 
 mode: coq 
 coq-prog-name: "/usr/local/coq-7.4/bin/coqtop -emacs -q"
 compile-command: "make matrix.vo"
 End:
*)
