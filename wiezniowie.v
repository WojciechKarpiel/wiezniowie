From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
DO POSPRZĄTANIA! KOD PONIŻEJ DZIAŁA I DOWODZI, CO MA DOWODZIĆ, ALE JEST STRASZNY BAŁAGAN

DOZRO:
[] opisać model (więźniowie + podanie rozwiązania 

*)


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
    move => x y z.  apply: eqP. rewrite /Zp_add /inZp /eq_op /=.
    rewrite modnDml modnDmr. rewrite addnA //.
  Qed.

  Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
    move =>x. apply: eqP. rewrite /Zp_add /inZp /eq_op /=.
    rewrite modnDml subnK. rewrite modnn //.
    case: x => [x d  ] /=.
      by apply: ltnW.
  Qed.
  
  Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
  Canonical Zp_zmodType := ZmodType 'I_n Zp_zmodMixin. 
End  CalkowiteModulo.

(* Tutaj jest mięsko *)
Section Wiezniowie.
  Variable n' : nat.
  Notation n := n'.+1.
  Variable wiezniowie : n.-tuple 'I_n.

  Open Scope ring_scope.

  Definition suma_modulo (ziomy : seq 'I_n): 'I_n :=
    (*\sum_(i <- ziomy) i. *) (* to się źle redukuje, ocb *)
    foldr (fun a b => a + b) ord0 ziomy.

  Definition algorytm_wieznia  := 'I_n -> (n'.-tuple 'I_n ) -> 'I_n.

  (* to jest poprawne, ale może być ciężkie w użyciu, będzie do obczajenia *)
  Definition bez_niego  (lp: 'I_n): n'.-tuple 'I_n.
    refine (@Tuple n' _ (behead [tuple of (rot lp wiezniowie)]) _).
    rewrite size_behead size_rot size_tuple //.
  Defined.

  Definition z_nim (lp : 'I_n) (bezn: n'.-tuple 'I_n) : n.-tuple 'I_n.
    refine (@Tuple n _ (rotr lp ((*tnth wiezniowie lp*)(thead [tuple of (rot lp wiezniowie)])  :: bezn)) _).
    rewrite size_rotr /= size_tuple //. 
  Defined.

  Lemma bezKq: forall lp :'I_n, z_nim lp (bez_niego lp) == wiezniowie.
    move => lp.
    rewrite /bez_niego /z_nim .
    rewrite /eq_op /=.
    have -> : behead (rot lp wiezniowie) =   behead [tuple of(rot lp wiezniowie)].
    apply: f_equal.
    apply /eqP.  done.
    have -> : (rotr lp    (thead [tuple of rot lp wiezniowie] :: behead [tuple of rot lp wiezniowie]))
             =  (rotr lp  [tuple of  (thead [tuple of rot lp wiezniowie] :: behead [tuple of rot lp wiezniowie])]).
    apply: f_equal. apply /eqP. done.
    rewrite -(tuple_eta [tuple of rot lp wiezniowie]).
    rewrite rotK.
    done.
  Qed.
  Lemma bezK: forall lp :'I_n, z_nim lp (bez_niego lp) = wiezniowie.
    move => lp.
    exact (eqP (bezKq lp)).
  Qed.
  


  Definition zgadza_sie (algo :algorytm_wieznia) (w: 'I_n) := (tnth wiezniowie w) ==  (algo w (bez_niego w)).
  Definition poprawne_rozw (algo :algorytm_wieznia):Prop := ex (zgadza_sie algo) .

  Definition poprawne_rozwb (algo :algorytm_wieznia):bool :=
    has (fun w => zgadza_sie algo w) (ord_tuple n).


  Definition dopełnij_do (co: 'I_n) (do_ : 'I_n) : 'I_n := do_ - co.
  
  (* Rozwiązanie zagadki *)
  Definition poprawne_algo: algorytm_wieznia :=
    fun lp pozostali => dopełnij_do (suma_modulo pozostali) lp.


  (* to będzie do wywalenia się, gdy ogarnę, które lematy odpowiadają za manipulację notacjami, których używam xD *)
  Lemma żalżal (x y : 'I_n): x + y = Zp_add x y.
    done.
  Qed.

  Lemma suma_modulo_cat s1 s2 : suma_modulo (s1 ++ s2) = (suma_modulo s1 + suma_modulo s2).
  Proof.
    elim: s1 => //=; [  rewrite żalżal Zp_add0z //|].
    move => x s1 ->. rewrite !żalżal  Zp_addA //.
  Qed.

  (* suma modulo olewa permutacje *)
  Lemma rotr_niet p q: perm_eq   p q -> suma_modulo p = suma_modulo q.

    apply/catCA_perm_subst: p q => s1 s2 s3.
    rewrite !suma_modulo_cat. rewrite {1}żalżal {1}żalżal.
    rewrite Zp_addA. rewrite (Zp_addC (suma_modulo s1) (suma_modulo s2)). rewrite  -Zp_addA.
    done.
  Qed.

  Lemma smodp s a : a + suma_modulo s = suma_modulo (a :: s).
    done.
  Qed.

  (* Bool.negb_involutive , ale nie chce bo zniemisiowanie mózgowe *)
  Lemma nienienienie b : ~~ ~~ b = b.
  Proof. by case: b. Qed.
  Lemma niepełna_suma lp : suma_modulo wiezniowie = (tnth wiezniowie lp) + suma_modulo (bez_niego lp).
    rewrite -{1}(bezK lp) /z_nim /=.
    rewrite smodp.
    apply: rotr_niet.
    rewrite  perm_rot.
    suff ->: thead [tuple of rot lp wiezniowie] = tnth wiezniowie lp.
    rewrite perm_cons perm_refl //.
    rewrite /rot /thead.

    rewrite !(tnth_nth ord0).

    rewrite nth_cat.
    case: ifP .

    move => _.
    rewrite nth_drop.
    rewrite addn0 //.
    (**)

    
    rewrite ltnNge /=.
    rewrite -[false]/(~~ true).
    move => d.
    apply (f_equal (fun x => ~~ x) ) in d.

    rewrite !nienienienie in d.

    rewrite leqn0 in d.
    exfalso.
    rewrite size_drop in d.

    rewrite subn_eq0 in d.
    pose xd := ltn_ord lp.
    rewrite size_tuple in d.

    suff: lp < lp.
      by rewrite ltnn.

      apply: leq_ltn_trans d. exact xd.
  Qed.


  
  (* 
więzień w zgaduje, że suma_modulo to w.
więc, jeśli suma_modulo to w, to więzień w zgadnie, co ma na czole

   *)
  Lemma wiezien_zgadl  (w : 'I_n)
        (elo: suma_modulo wiezniowie = w) : zgadza_sie poprawne_algo w.
    rewrite /zgadza_sie /poprawne_algo /dopełnij_do.
    rewrite -{2}elo (niepełna_suma w).
    rewrite !żalżal -Zp_addA. rewrite [(Zp_add (suma_modulo (bez_niego w)) (- suma_modulo (bez_niego w)))]Zp_addC. rewrite Zp_addNz Zp_addC Zp_add0z  //.
  Qed.

  Lemma wiezien_zgadl': zgadza_sie poprawne_algo (suma_modulo wiezniowie).
      by     apply: wiezien_zgadl.
  Qed.
  Print wiezien_zgadl'.

  Lemma wiezien_zgadl'': poprawne_rozw poprawne_algo.
  Proof.
    exists (suma_modulo wiezniowie).
    apply: wiezien_zgadl'.
  Qed.
  Print wiezien_zgadl''.
  Close Scope ring_scope.
End Wiezniowie.

(* wsyzstkie możliwe rozw 'I_n -> x-tuple -> x+1 -tuple*)
Definition rozwiń (n: nat) (p: nat) (tpl : p.-tuple 'I_n): n.-tuple ( p.+1.-tuple 'I_n) :=
  [tuple of (map (fun x => [tuple of (x :: tpl)]) (ord_tuple n))].


Lemma rozwiazanie_dziala_zawsze : forall n' : nat, forall wiezniowie: (n'.+1).-tuple 'I_n'.+1, poprawne_rozw wiezniowie (@poprawne_algo n').
Proof. exact wiezien_zgadl''. Qed.

