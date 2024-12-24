require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1636366 : Prf (∀ (λ d1 : El real, (∀ (λ d2 : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) d1) (real_lt (real_of_num (NUMERAL _0)) d2)) (∃ (λ e : El real, (∧ (real_lt (real_of_num (NUMERAL _0)) e) (∧ (real_lt e d1) (real_lt e d2))))))))));
