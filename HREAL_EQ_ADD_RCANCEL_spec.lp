require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1321459 : Prf (∀ (λ m : El hreal, (∀ (λ n : El hreal, (∀ (λ p : El hreal, (= (= (hreal_add m p) (hreal_add n p)) (= m n))))))));
