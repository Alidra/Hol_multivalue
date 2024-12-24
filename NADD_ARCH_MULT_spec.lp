require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1286557 : Prf (∀ (λ x : El nadd, (∀ (λ k : El num, (⇒ (¬ (nadd_eq x (nadd_of_num (NUMERAL _0)))) (∃ (λ N : El num, (nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N) x)))))))));
