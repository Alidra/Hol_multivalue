require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7214061 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∀ (λ i : El num, (⇒ (∧ (<= m i) (<= i n)) (= (f i) (real_of_num (NUMERAL _0)))))) (= ((@sum num) (… m n) f) (real_of_num (NUMERAL _0))))))))));
