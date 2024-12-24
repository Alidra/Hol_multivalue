require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2743639 (q : El int) (m : El int) (n : El int) (r : El int) : Prf (⇒ (= (int_add (int_mul q n) r) m) (⇒ (int_le (int_of_num (NUMERAL _0)) r) (⇒ (int_lt r (int_abs n)) (∧ (= (div m n) q) (= (rem m n) r)))));
