require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070360 : Prf (∀ (λ x : El int, (∀ (λ p : El int, (∀ (λ m : El num, (∀ (λ n : El num, (= (rem (rem x (int_pow p m)) (int_pow p n)) (rem x (int_pow p (MIN m n))))))))))));
