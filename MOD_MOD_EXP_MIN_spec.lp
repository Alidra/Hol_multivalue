require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem235568 : Prf (∀ (λ x : El num, (∀ (λ p : El num, (∀ (λ m : El num, (∀ (λ n : El num, (= (MOD (MOD x (EXP p m)) (EXP p n)) (MOD x (EXP p (MIN m n))))))))))));
