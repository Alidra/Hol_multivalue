require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1301912 : Prf (∀ (λ x : El nadd, (⇒ (¬ (nadd_eq x (nadd_of_num (NUMERAL _0)))) (∃ (λ A : El num, (∃ (λ B : El num, (∀ (λ n : El num, (<= (nadd_rinv x n) (+ (* A n) B)))))))))));
