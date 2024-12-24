require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7221508 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (∀ (λ p : El num, (⇒ (∧ (<= m p) (<= p n)) (real_le (real_of_num (NUMERAL _0)) (f p))))) (= ((@sum num) (… m n) f) (real_of_num (NUMERAL _0)))) (∀ (λ p : El num, (⇒ (∧ (<= m p) (<= p n)) (= (f p) (real_of_num (NUMERAL _0)))))))))))));
