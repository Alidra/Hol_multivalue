require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2427003 : Prf (∀ (λ n : El int, (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ c : El int, (∀ (λ d : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (⇒ (∧ (= a b) (¬ (= c d))) (¬ (= (int_add a (int_mul n c)) (int_add b (int_mul n d))))))))))))))));
