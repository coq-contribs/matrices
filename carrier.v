Require Export ZArithRing.

Module Type Carrier.
Parameter A : Set.
Parameter Aopp : A -> A.
Parameters (Aplus : A -> A -> A) (Amult : A -> A -> A).
Parameters (A0 : A) (A1 : A).
Parameter Aeq : A -> A -> bool.
(* unused, should be [x,y:A]false *)
 
Axiom A_ring : Ring_Theory Aplus Amult A1 A0 Aopp Aeq.

Add Abstract Ring A Aplus Amult A1 A0 Aopp Aeq A_ring.

End Carrier.


Module Zc : Carrier.

Definition A := Z.
Definition Aopp := Zopp.
Definition Aplus := Zplus.
Definition Amult := Zmult.
Definition A0 := 0%Z.
Definition A1 := 1%Z.
Definition Aeq := Zeq.

Definition A_ring := ZTheory.

End Zc.

 
  (*
  Local Variables: 
  mode: coq 
  coq-prog-name: "/usr/local/coq-7.4/bin/coqtop -emacs -q"
  compile-command: "make carrier.vo"
  End:
  *)