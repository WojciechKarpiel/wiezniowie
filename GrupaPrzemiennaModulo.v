From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Poniższa sekcja to kopia rozdziału 8.1 z "Math Components Book" (https://math-comp.github.io/mcb/)
Nie mogłem tego znaleźć w bibliotece
 *)
Section CalkowiteModulo.
  Variable n' : nat.
  Notation n := n'.+1.

  Implicit Types x y : 'I_n.
  Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn n')).
  
  Definition Zp0 : 'I_n := ord0.
  Definition Zp1 := inZp 1.
  Definition Zp_opp x := inZp (n - x).
  Definition Zp_add x y := inZp (x + y).
  Definition Zp_mul x y := inZp (x * y).

  Lemma Zp_add0z : left_id Zp0 Zp_add.
  Proof.
      by move => x; apply: eqP; rewrite /Zp_add add0n /inZp /eq_op /= modn_small.
  Qed.

  Lemma Zp_mulC : commutative Zp_mul.
  Proof.
      by move => x y; apply: eqP; rewrite /Zp_mul /inZp /eq_op /= mulnC.
  Qed.

  Lemma Zp_addC : commutative Zp_add.
  Proof.
      by move => x y; apply: eqP; rewrite /Zp_add /inZp /eq_op /= addnC.
  Qed.

  Lemma Zp_addA : associative Zp_add.
  Proof.
    move => x y z; apply: eqP. rewrite /Zp_add /inZp /eq_op /=.
    rewrite modnDml modnDmr; rewrite addnA //.
  Qed.

  Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
    move => x; apply: eqP. rewrite /Zp_add /inZp /eq_op /=.
    rewrite modnDml subnK. rewrite modnn //.
    case: x => [x d  ] /=.
      by apply: ltnW.
  Qed.
  
  Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
  Canonical Zp_zmodType := ZmodType 'I_n Zp_zmodMixin. 
End  CalkowiteModulo.
