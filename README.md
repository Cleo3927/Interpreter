Rozwiązanie jest oparte na języku Latte. 
Implementacja Typecheckera znajduje się w pliku Checker.hs. Jego zadaniem jest sprawdzanie:
- poprawności typów
- istnienia funkcji
- sprawdzanie zwracanych typow przez funkcje
- sprawdzanie czy funkcja zwraca parametry
- sprawdzanie poprawności parametrów funkcji

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
Do 30: Aktualnie 12, 16

Oczekiwany wynik: 25 :)