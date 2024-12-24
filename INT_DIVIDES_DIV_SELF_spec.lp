require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2730195 : Prf (∀ (λ n : El int, (∀ (λ d : El int, (⇒ (int_divides d n) (int_divides (div n d) n))))));
