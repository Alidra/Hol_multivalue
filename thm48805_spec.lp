require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48805 [A] (a : El A) (b : El A) : Prf ((λ b' : El A, (= (= a b') ((@GEQ A) a b'))) b);
