require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1263160 : Prf (∀ (λ x : El nadd, (∃ (λ A : El num, (∃ (λ B : El num, (∀ (λ n : El num, (<= (dest_nadd x n) (+ (* A n) B))))))))));
