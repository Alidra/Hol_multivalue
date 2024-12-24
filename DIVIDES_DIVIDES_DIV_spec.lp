require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3113121 : Prf (∀ (λ n : El num, (∀ (λ d : El num, (∀ (λ e : El num, (⇒ (num_divides d n) (= (num_divides e (DIV n d)) (num_divides (* d e) n)))))))));
