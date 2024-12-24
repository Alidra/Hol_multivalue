require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1299579 : Prf (∀ (λ x : El nadd, (∃ (λ B : El num, (∃ (λ N : El num, (∀ (λ n : El num, (⇒ (<= N n) (<= (dest_nadd x n) (* B n)))))))))));
