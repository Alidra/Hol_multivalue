require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2310536 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ c : El int, (= (int_add (int_sub a b) (int_sub b c)) (int_sub a c))))))));
