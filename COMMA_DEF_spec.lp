require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem45466 [A B] : Prf (∀ (λ x : El A, (∀ (λ y : El B, (= ((@̦‚ A B) x y) ((@ABS_prod A B) ((@mk_pair A B) x y)))))));
