require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1321767 : Prf (∀ (λ m : El hreal, (∀ (λ n : El hreal, (∀ (λ p : El hreal, (= (hreal_mul (hreal_add m n) p) (hreal_add (hreal_mul m p) (hreal_mul n p)))))))));
