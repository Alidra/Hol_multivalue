require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2740831 : Prf (∀ (λ n : El int, (∀ (λ d : El int, (∀ (λ e : El int, (⇒ (int_divides d n) (= (int_divides e (div n d)) (int_divides (int_mul d e) n)))))))));
