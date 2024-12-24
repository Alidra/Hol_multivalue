require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3086875 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (num_divides m n) (∨ (∧ (<= (NUMERAL (BIT1 _0)) m) (<= m n)) (= n (NUMERAL _0))))))));
