require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem466 [A B] : Prf (∀ (λ t1 : El A, (∀ (λ t2 : El B, (= ((λ x : El B, t1) t2) t1)))));
