# Więźniowie

Repo zawiera rozwiązanie i dowód formalny poprawności rozwiązania zagadki logicznej o więźniach


## Treść zagadki

W więzieniu było N więźniów. Naczelnik ogłosił więźniom, że mają szansę odzyskać wolność,
jeśli sprostają wyzwaniu. Naczelnik przedstawił więźniom następujące zasady wyzwania:

1. Naczelnik da więźniom kilka dni do namysłu i ustalenia strategii
1. Gdy czas do namysłu się skończy, więźniowie dostaną zakaz jakiejkolwiek komunikacji między sobą
1. Naczelnik napisze na czole każdego z więźniów liczbę od 0 do N-1, liczby mogą się powtarzać
1. Każdy z więźniów będzie widział liczby na czołach pozostałych współwięźniów, ale nie będzie widział swojej
1. Więźniowie będą po kolei szeptali na ucho naczelnikowi domniemaną odpowiedź na pytanie: "Jaką liczbę masz na czole?"
1. Jeśli co najmniej jeden z więźniów zgadnie, wszyscy odzyskują wolność

Jaka jest optymalna strategia dla więźniów? W jakich przypadkach zadziała, a w jakich nie?

Źródło zagadki: nie wiem, znalazłem tą zagadkę na zkserowanym fragmencie kartki w formie bajki o Pawle i Gawle. Jeśli ktoś zna źródło to proszę o podanie

## Rozwiązanie

[Tutaj](rozwiazanie.md) jest opis słowno-muzyczny, a dowód formalny w pliku [wiezniowie.v](wiezniowie.v).
