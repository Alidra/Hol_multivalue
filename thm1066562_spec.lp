require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066562 [A] (a : El A) (f : El (fun num A)) (n : El num) : Prf (= ((λ n' : El num, (= ((@FCONS A) a f (SUC n')) (f n'))) n) (= ((@FCONS A) a f (SUC n)) (f n)));
