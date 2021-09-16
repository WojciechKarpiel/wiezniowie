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

  (* Rozwiązanie zagadki - wyjaśnienie w "rozwiazanie.md" *)
  (* Z taką definicją pracuje się łatwiej niż z: \sum_(i <- liczby) i *)
  Definition suma_modulo (liczby : seq 'I_n): 'I_n :=  foldr (fun a b => a + b) ord0 liczby.
  Definition algorytm_wygrywajacy: rozwiazanie :=
    fun lp pozostali => lp - (suma_modulo pozostali).

  (* Poniżej są już tylko lematy przygotowujące do ostatecznego twierdzenia, że algorytm_wygrywajacy jest zawsze poprawnym rozwiązaniem *)
  
  
  (* przywróć więźnia spowrotem do puli, po wycięciu go. Konstrukcja jest taka, aby łatwo było dowieźć lemat o odwracalności przywroc_pozostali  *)
  Definition przywroc (lp : 'I_n) (pozostali: n.-1.-tuple 'I_n) : n.-tuple 'I_n :=
    [tuple of rotr lp (thead [tuple of rot lp wiezniowie] :: pozostali)].

  Lemma przywroc_pozostali  (lp :'I_n): przywroc lp (pozostali lp) = wiezniowie.
    apply /eqP; rewrite /pozostali /przywroc /eq_op /=.
    rewrite -[rotr lp [tuple of thead [tuple of rot lp wiezniowie] :: behead [tuple of rot lp wiezniowie]]]/_.
    rewrite -tuple_eta rotK //.
  Qed.

  (* suma modulo jest rozdzielna ze względu na łączenie krotek *)
  Lemma suma_modulo_plusplus s1 s2 : suma_modulo (s1 ++ s2) = (suma_modulo s1 + suma_modulo s2).
  Proof.
    by elim: s1 => /=; [rewrite GRing.add0r | move => x s1 ->; rewrite GRing.addrA].
  Qed.

  (* suma modulo jest taka sama dla wsystkich permutacji krotki *)
  Lemma suma_modulo_perm p q: perm_eq p q -> suma_modulo p = suma_modulo q.
    apply/catCA_perm_subst: p q => s1 s2 s3.
    rewrite !suma_modulo_plusplus GRing.addrA [(_ s1) + (_ s2)]GRing.addrC GRing.addrA //.
  Qed.

  Lemma suma_modulo_cons s a : a + suma_modulo s = suma_modulo (a :: s). done. Qed.

  (* jeśli dorzuci się liczbę na czole więźnia do sumy modulo pozostałych, to otrzyma się sumę modulo wszystkich *)
  Lemma suma_modulo_pozostalych lp : suma_modulo wiezniowie = (tnth wiezniowie lp) + suma_modulo (pozostali lp).
    rewrite -{1}(przywroc_pozostali lp) /przywroc /= suma_modulo_cons.
    apply: suma_modulo_perm.
    rewrite  perm_rot.
    suff ->: thead [tuple of rot lp wiezniowie] = tnth wiezniowie lp by rewrite perm_cons perm_refl.
    rewrite /rot /thead !(tnth_nth ord0) nth_cat.
    case: ifP; [rewrite nth_drop addn0 |
                (* (val 'I_n) będzie zawsze mniejsze niż (size_tuple n-tuple) *)
                rewrite ltnNge leqn0 size_drop subn_eq0 size_tuple -leqNgt -[lp <= n']/(lp < n) ltn_ord];
    done.
  Qed.
  
  Lemma algorytm_wygrywajacy_jest_zawsze_poprawny: poprawne_rozwiazanie algorytm_wygrywajacy.
  Proof.
    rewrite /poprawne_rozwiazanie /algorytm_wygrywajacy /zgadl.
    exists (suma_modulo wiezniowie).
    rewrite {2}(suma_modulo_pozostalych (suma_modulo wiezniowie)).
    rewrite  -GRing.addrA GRing.addrN GRing.addr0 //. 
  Qed.
End Wiezniowie.
Close Scope ring_scope.

(* Tak dla pewności, powtórzenie tego samego poza sekcją *)
Lemma rozwiazanie_dziala_zawsze :
  forall (n' : nat) (wiezniowie: (n'.+1).-tuple 'I_n'.+1),
    poprawne_rozwiazanie wiezniowie (@algorytm_wygrywajacy n').
Proof. exact algorytm_wygrywajacy_jest_zawsze_poprawny. Qed.
