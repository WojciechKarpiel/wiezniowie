# Rozwiązanie zgadki

Istnieje strategia, która zawsze gwarantuje więźniom odzyskanie wolności.

Więźniowie muszą sami siebie ponumerować od 0 do N-1.
Niech `w_i` oznacza i-ty więzień ma na czole liczbę "w\_i".
"i-ty" więzień zgaduje, że suma liczb na czołach wszystkich modulo N to "i", czyli, że:

    i =[mod N]= w_0 + w_1 + ... + w_(i-1) + w_i + w_(i+1) + ... + w_(N-2) + w_(N-1)
    
"i-ty" więzień nie zna `w_i`, ale zna liczby na czołach pozostałych oraz swój numer (`i`), zatem może policzyć:

    w_i =[mod N]= i - (w_0 + w_1 + ... + w_(i-1) + w_(i+1) + ... + w_(N-2) + w_(N-1))

Suma liczb na czołach modulo N może przyjąć N różnych wartości. Skoro jest N więźniów i każdy z więźniów zgaduje inną wartość sumy, to dokładnie jeden z nich zgadnie!
