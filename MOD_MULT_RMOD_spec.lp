require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem205654 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (* m (MOD p n)) n) (MOD (* m p) n))))))));
