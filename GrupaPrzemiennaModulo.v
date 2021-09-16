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

  Ltac odwin := intro x; intros; apply: eqP; rewrite /Zp_add /Zp_mul /inZp /eq_op /=.
  
  Lemma Zp_add0z : left_id Zp0 Zp_add.
  Proof.
      by odwin; rewrite add0n modn_small.
  Qed.

  Lemma Zp_mulC : commutative Zp_mul.
  Proof.
      by odwin; rewrite mulnC.
  Qed.

  Lemma Zp_addC : commutative Zp_add.
  Proof.
      by odwin; rewrite addnC.
  Qed.

  Lemma Zp_addA : associative Zp_add.
  Proof.
      by odwin; rewrite modnDml modnDmr addnA.
  Qed.

  Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
      by odwin; rewrite modnDml subnK; [rewrite modnn | apply: ltnW; rewrite ltn_ord].
  Qed.
  
  Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
  Canonical Zp_zmodType := ZmodType 'I_n Zp_zmodMixin. 
End CalkowiteModulo.
