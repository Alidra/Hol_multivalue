require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300922 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ c : El int, (∀ (λ d : El int, (= (int_sub (int_add a b) (int_add c d)) (int_add (int_sub a c) (int_sub b d)))))))))));
