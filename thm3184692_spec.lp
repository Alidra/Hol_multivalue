require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3184692 [_83123] (P : El (fun (fun bool (fun _83123 bool)) bool)) (x : El _83123) : Prf (= (P ((@SETSPEC _83123) x)) (P (λ p : El bool, (λ t : El _83123, (∧ p (= x t))))));
