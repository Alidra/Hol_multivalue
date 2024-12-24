require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3088029 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (num_divides m n) (⇒ (= n (NUMERAL _0)) (= m (NUMERAL _0)))) (<= m n))))));
