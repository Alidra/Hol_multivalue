require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem183010 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (MOD (MOD m n) n) (MOD m n))))));
