require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1633184 : Prf (∀ (λ x : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt x (real_of_num (NUMERAL (BIT1 _0))))) (real_lt (real_of_num (NUMERAL (BIT1 _0))) (real_inv x)))));
