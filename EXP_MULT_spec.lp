require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem88950 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (EXP m (* n p)) (EXP (EXP m n) p))))))));
