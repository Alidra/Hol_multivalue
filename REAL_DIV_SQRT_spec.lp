require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1965641 : Prf (∀ (λ x : El real, (⇒ (real_le (real_of_num (NUMERAL _0)) x) (= (real_div x (sqrt x)) (sqrt x)))));
