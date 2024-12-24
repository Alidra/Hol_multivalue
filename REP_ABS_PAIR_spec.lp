require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem45455 [A B] : Prf (∀ (λ x : El A, (∀ (λ y : El B, (= ((@REP_prod A B) ((@ABS_prod A B) ((@mk_pair A B) x y))) ((@mk_pair A B) x y))))));
