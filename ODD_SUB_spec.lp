require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem145719 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (ODD (- m n)) (∧ (< n m) (¬ (= (ODD m) (ODD n)))))))));
