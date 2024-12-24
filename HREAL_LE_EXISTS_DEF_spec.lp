require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1321284 : Prf (∀ (λ m : El hreal, (∀ (λ n : El hreal, (= (hreal_le m n) (∃ (λ d : El hreal, (= n (hreal_add m d)))))))));
