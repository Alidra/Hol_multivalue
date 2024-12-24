require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem206228 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (EXP (MOD m n) p) n) (MOD (EXP m p) n))))))));
