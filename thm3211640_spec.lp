require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211640 [_83095] (p : El (fun _83095 bool)) (x : El _83095) : Prf ((λ x' : El _83095, (= ((@IN _83095) x' ((@GSPEC _83095) (λ v : El _83095, (∃ (λ y : El _83095, ((@SETSPEC _83095) v (p y) y)))))) (p x'))) x);
