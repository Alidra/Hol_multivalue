require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem70828 : Prf (∀ (λ x1 : El ind, (∀ (λ x2 : El ind, (= (= (IND_SUC x1) (IND_SUC x2)) (= x1 x2))))));
