require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem88509 : Prf (∀ (λ p : El num, (∀ (λ m : El num, (∀ (λ n : El num, (= (EXP (* m n) p) (* (EXP m p) (EXP n p)))))))));
