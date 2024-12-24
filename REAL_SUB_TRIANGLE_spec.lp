require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1520119 : Prf (∀ (λ a : El real, (∀ (λ b : El real, (∀ (λ c : El real, (= (real_add (real_sub a b) (real_sub b c)) (real_sub a c))))))));
