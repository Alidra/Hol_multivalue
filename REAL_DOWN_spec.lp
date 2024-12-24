require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1634773 : Prf (∀ (λ d : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) d) (∃ (λ e : El real, (∧ (real_lt (real_of_num (NUMERAL _0)) e) (real_lt e d)))))));
