require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1321588 : Prf (∀ (λ m : El hreal, (∀ (λ n : El hreal, (∀ (λ p : El hreal, (= (hreal_le (hreal_add m n) (hreal_add m p)) (hreal_le n p))))))));
