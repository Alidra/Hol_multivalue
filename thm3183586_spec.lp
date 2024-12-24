require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3183586 [_83152] (p : El (fun _83152 bool)) (x : El _83152) : Prf (= (= (∃ (λ y : El _83152, (∧ (p y) (= x y)))) (p x)) (= (∃ (λ y : El _83152, ((@SETSPEC _83152) x (p y) y))) (p x)));
