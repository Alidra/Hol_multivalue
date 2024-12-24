require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem137108 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (* (- m n) p) (- (* m p) (* n p)))))))));
