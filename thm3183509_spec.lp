require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3183509 [_83095] (p : El (fun _83095 bool)) (x : El _83095) : Prf (= (= (∃ (λ y : El _83095, (∧ (p y) (= x y)))) (p x)) (= (∃ (λ y : El _83095, ((@SETSPEC _83095) x (p y) y))) (p x)));
