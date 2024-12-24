require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1299985 : Prf (∀ (λ x : El nadd, (⇒ (¬ (nadd_eq x (nadd_of_num (NUMERAL _0)))) (∃ (λ N : El num, (∀ (λ n : El num, (⇒ (<= N n) (¬ (= (dest_nadd x n) (NUMERAL _0)))))))))));
