require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem125496 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (EVEN (+ m n)) (= (EVEN m) (EVEN n)))))));
