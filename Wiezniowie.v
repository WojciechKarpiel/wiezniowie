From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import GrupaPrzemiennaModulo.


(* UWAGA: Dowody lematów w trakcie sprzątania, na razie są zabałaganione i przydługie *)

Open Scope ring_scope.
Section Wiezniowie.
  (* W więzieniu jest n więźniów. Zakładamy, że n > 0 *)
  Variable n' : nat.
  Notation n := n'.+1.

  (* Każdy więzień ma na czole liczbę od 0 do n (czyli spośród 'I_n) *)
  Variable wiezniowie : n.-tuple 'I_n.

  (* Postać rozwiązania to rodzina algorytmów.
     Indeksem rodziny jest numer więźnia (0..N-1) - pierwszy argument.
     Wejściem algorytmu są liczby widziane na czołach pozostałych (krotka n-1 liczb) - drugi argument.
     Wyjściem algorytmu jest domniemana liczba na czole więźnia.
   *)
  Definition rozwiazanie := (* numer więźnia *) 'I_n ->
                            (* liczby widziane u pozostałych *) n.-1.-tuple 'I_n ->
                            (* domanimana liczba na swoim czole *) 'I_n.


  (* Wycięcie więźnia w taki sposób to szczegół techniczny, można by to robić jakkolwiek inaczej, o ile byłby lemat o odwracalności (przywroc_pozostali) *)
  Definition pozostali (lp: 'I_n): n.-1.-tuple 'I_n := [tuple of (behead (rot lp wiezniowie))].

  (* Więzień zgadł, jeśli liczba na jego czole jest taka, jaką policzył jego algorytm *)
  Definition zgadl (algorytm :rozwiazanie) (lp: 'I_n) :=
    tnth wiezniowie lp == algorytm lp (pozostali lp).

  Definition poprawne_rozwiazanie (algorytm :rozwiazanie): Prop := exists wiezien, zgadl algorytm wiezien.

 (* TUTAJ POPRAWNE ALGO? *)

  (* przywróć więźnia spowrotem do puli, po wycięciu go. Konstrukcja jest taka, aby łatwo było dowieźć lemat o odwracalności przywroc_pozostali  *)
  Definition przywroc (lp : 'I_n) (pozostali: n.-1.-tuple 'I_n) : n.-tuple 'I_n :=
    [tuple of rotr lp (thead [tuple of rot lp wiezniowie] :: pozostali)].

    Lemma przywroc_pozostali  (lp :'I_n): przywroc lp (pozostali lp) = wiezniowie.
      rewrite /pozostali /przywroc .
      apply /eqP.
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

  (* PONIŻEJ JEST NIE POSPRZĄTANE, CIĘŻKIE DO CZYTNIA *)
  
  
  
  
  





  Definition dopełnij_do (co: 'I_n) (do_ : 'I_n) : 'I_n := do_ - co.

    (* Z taką definicją pracuje się łatwiej niż z: \sum_(i <- liczby) i *)
  Definition suma_modulo (liczby : seq 'I_n): 'I_n :=  foldr (fun a b => a + b) ord0 liczby.

  (* Rozwiązanie zagadki *)
  Definition poprawne_algo: rozwiazanie :=
    fun lp pozostali => dopełnij_do (suma_modulo pozostali) lp.


  Lemma suma_modulo_cat s1 s2 : suma_modulo (s1 ++ s2) = (suma_modulo s1 + suma_modulo s2).
  Proof.
    elim: s1 => //=; [   rewrite GRing.add0r //|].
    move => x s1 ->. rewrite GRing.addrA //.
  Qed.

  (* suma modulo olewa permutacje *)
  Lemma rotr_niet p q: perm_eq   p q -> suma_modulo p = suma_modulo q.

    apply/catCA_perm_subst: p q => s1 s2 s3.
    rewrite !suma_modulo_cat.
    rewrite GRing.addrA. rewrite (GRing.addrC (suma_modulo s1) (suma_modulo s2)). rewrite  -GRing.addrA.
    done.
  Qed.

  Lemma smodp s a : a + suma_modulo s = suma_modulo (a :: s).
    done.
  Qed.

  Lemma niepełna_suma lp : suma_modulo wiezniowie = (tnth wiezniowie lp) + suma_modulo (pozostali lp).
    rewrite -{1}(przywroc_pozostali lp) /przywroc /=.
    rewrite smodp.
    apply: rotr_niet.
    rewrite  perm_rot.
    suff ->: thead [tuple of rot lp wiezniowie] = tnth wiezniowie lp.
    rewrite perm_cons perm_refl //.
    rewrite /rot /thead.

    rewrite !(tnth_nth ord0).

    rewrite nth_cat.
    case: ifP; [rewrite nth_drop addn0 |
                (* (val 'I_n) będzie zawsze mniejsze niż (size_tuple n-tuple) *)
                rewrite ltnNge leqn0 size_drop subn_eq0 size_tuple -leqNgt -[lp <= n']/(lp < n) ltn_ord];
    done.
  Qed.
  
  
  (* 
więzień w zgaduje, że suma_modulo to w.
więc, jeśli suma_modulo to w, to więzień w zgadnie, co ma na czole

   *)
  Lemma wiezien_zgadl  (w : 'I_n)
        (elo: suma_modulo wiezniowie = w) : zgadl poprawne_algo w.
    rewrite /zgadl /poprawne_algo /dopełnij_do.
    rewrite -{2}elo (niepełna_suma w).
    rewrite  -GRing.addrA. rewrite [( (suma_modulo (pozostali w)) + (- suma_modulo (pozostali w)))]GRing.addrC.
    rewrite GRing.addNr GRing.addr0 //. 
  Qed.

  Lemma wiezien_zgadl': zgadl poprawne_algo (suma_modulo wiezniowie).
      by     apply: wiezien_zgadl.
  Qed.
  Print wiezien_zgadl'.

  Lemma wiezien_zgadl'': poprawne_rozwiazanie poprawne_algo.
  Proof.
    exists (suma_modulo wiezniowie).
    apply: wiezien_zgadl'.
  Qed.
  Print wiezien_zgadl''.

End Wiezniowie.

(* wsyzstkie możliwe rozw 'I_n -> x-tuple -> x+1 -tuple*)
Definition rozwiń (n: nat) (p: nat) (tpl : p.-tuple 'I_n): n.-tuple ( p.+1.-tuple 'I_n) :=
  [tuple of (map (fun x => [tuple of (x :: tpl)]) (ord_tuple n))].


Lemma rozwiazanie_dziala_zawsze : forall n' : nat, forall wiezniowie: (n'.+1).-tuple 'I_n'.+1, poprawne_rozwiazanie wiezniowie (@poprawne_algo n').
Proof. exact wiezien_zgadl''. Qed.

Close Scope ring_scope.
