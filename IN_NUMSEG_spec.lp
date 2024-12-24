require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5371273 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= ((@IN num) p (… m n)) (∧ (<= m p) (<= p n)))))))));
