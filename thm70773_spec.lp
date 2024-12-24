require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem70773 : Prf (= IND_0 ((@ε ind) (λ z : El ind, (∧ (∀ (λ x1 : El ind, (∀ (λ x2 : El ind, (= (= (IND_SUC x1) (IND_SUC x2)) (= x1 x2)))))) (∀ (λ x : El ind, (¬ (= (IND_SUC x) z))))))));
