require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2534337 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (int_add (rem m p) (rem n p)) p) (rem (int_add m n) p))))))));
