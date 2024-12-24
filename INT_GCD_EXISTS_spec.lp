require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2794185 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∃ (λ d : El int, (∧ (int_divides d a) (∧ (int_divides d b) (∃ (λ x : El int, (∃ (λ y : El int, (= d (int_add (int_mul a x) (int_mul b y)))))))))))))));
