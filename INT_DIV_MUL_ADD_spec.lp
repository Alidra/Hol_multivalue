require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2704369 : Prf (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (= (div (int_add (int_mul m n) p) n) (int_add m (div p n)))))))))) (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (= (div (int_add (int_mul n m) p) n) (int_add m (div p n)))))))))) (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (= (div (int_add p (int_mul m n)) n) (int_add (div p n) m))))))))) (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (= (div (int_add p (int_mul n m)) n) (int_add (div p n) m))))))))))));
