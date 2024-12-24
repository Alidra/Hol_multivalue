require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem87724 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (EXP m (+ n p)) (* (EXP m n) (EXP m p)))))))));
