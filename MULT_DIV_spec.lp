require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3116331 : Prf (∧ (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (num_divides p m) (= (DIV (* m n) p) (* (DIV m p) n))))))))) (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (num_divides p n) (= (DIV (* m n) p) (* m (DIV n p)))))))))));
