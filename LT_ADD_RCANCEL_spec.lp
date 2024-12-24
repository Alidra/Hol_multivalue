require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem101179 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (< (+ m p) (+ n p)) (< m n))))))));
