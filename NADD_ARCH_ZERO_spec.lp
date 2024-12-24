require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1292368 : Prf (∀ (λ x : El nadd, (∀ (λ k : El nadd, (⇒ (∀ (λ n : El num, (nadd_le (nadd_mul (nadd_of_num n) x) k))) (nadd_eq x (nadd_of_num (NUMERAL _0))))))));
