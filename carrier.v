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


Require Export ZArithRing.
Require Export ZArith.

Module Type Carrier.
Parameter A : Set.
Parameter Aopp : A -> A.
Parameters (Aplus Aminus Amult: A -> A -> A).
Parameters (A0 : A) (A1 : A).
 
Axiom A_ring : ring_theory A0 A1 Aplus Amult Aminus Aopp (eq(A:=A)).

End Carrier.


Module Zc : Carrier.

Definition A := Z.
Definition Aopp := Zopp.
Definition Aplus := Zplus.
Definition Aminus := Zminus.
Definition Amult := Zmult.
Definition A0 := 0%Z.
Definition A1 := 1%Z.

Definition A_ring := InitialRing.Zth.

End Zc.

 
  (*
  Local Variables: 
  mode: coq 
  coq-prog-name: "/usr/local/coq-7.4/bin/coqtop -emacs -q"
  compile-command: "make carrier.vo"
  End:
  *)
