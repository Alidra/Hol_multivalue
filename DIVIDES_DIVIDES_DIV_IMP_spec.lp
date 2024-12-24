require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3114294 : Prf (∀ (λ n : El num, (∀ (λ d : El num, (∀ (λ e : El num, (⇒ (num_divides (* d e) n) (num_divides e (DIV n d)))))))));
