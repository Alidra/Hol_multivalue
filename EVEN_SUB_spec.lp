require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem145380 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (EVEN (- m n)) (∨ (<= m n) (= (EVEN m) (EVEN n))))))));
