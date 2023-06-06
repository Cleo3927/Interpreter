Rozwiązanie jest oparte na języku Latte. 
Implementacja Typecheckera znajduje się w pliku Checker.hs. Jego zadaniem jest sprawdzanie:
- poprawności typów
- istnienia funkcji
- istnienie zmiennych
- sprawdzanie zwracanych typow przez funkcje
- sprawdzanie czy funkcja zwraca parametry
- sprawdzanie poprawności parametrów funkcji
- sprawdzanie czy Main zwraca void
Typechecker sprawdza czy dana funkcja zawsze zwróci poprawną wartość, w szczególności jeśli wartość zwracana jest w if albo w while typechecker zwróci błąd, że wartość nie jest zawsze zwracana. Jeśli wartość zwracana jest w if-else wtedy jest poprawnie.  

Zmienne różnych typów i funkcje mogą mieć te same nazwy: np funkcja "$a()" i zmienna $a

Iplementacja wykonywania wyrażeń znajduje się w pliku Eval.hs.

Odpalenie interpretera:
./interpreter plik
albo
za pomocą standardowego wejścia np
./interpreter < plik

Komunikaty błędu są wypisywane na standardowe wyjście błędów i zawierają opis błędu oraz linijkę w której błąd wystąpił. 

Cechy:
Na 15: 1, 2, 3, 4, 5, 6, (wybrane: 7 - wartość/referencja)
Na 20: 9, 10, 11 
Do 30: Aktualnie 12(4pkt), 13(2pkt), 16(1pkt)

Oczekiwany wynik: 27