require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3112963 : Prf (∀ (λ n : El num, (∀ (λ d : El num, (⇒ (num_divides d n) (num_divides (DIV n d) n))))));
