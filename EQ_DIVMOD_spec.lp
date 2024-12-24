require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem163266 : Prf (∀ (λ p : El num, (∀ (λ m : El num, (∀ (λ n : El num, (= (∧ (= (DIV m p) (DIV n p)) (= (MOD m p) (MOD n p))) (= m n))))))));
