require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1102439 [_25350 _25351] (h : El _25351) (f : El (fun _25351 (fun _25350 _25350))) (t : El (list _25351)) (b : El _25350) : Prf ((λ b' : El _25350, (= ((@ITLIST _25350 _25351) f ((@CONS _25351) h t) b') (f h ((@ITLIST _25350 _25351) f t b')))) b);
