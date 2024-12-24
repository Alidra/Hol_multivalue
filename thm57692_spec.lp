require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem57692 [A B] (f : El (fun A B)) (x : El A) : Prf (= ((λ x' : El A, (= ((@LET A B) f x') (f x'))) x) (= ((@LET A B) f x) (f x)));
