require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48812 [A] (a : El A) (b : El A) : Prf (= ((λ b' : El A, (= ((@GEQ A) a b') (= a b'))) b) (= ((@GEQ A) a b) (= a b)));
