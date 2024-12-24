require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3117303 (P : El (fun int bool)) : Prf (∧ (= (∀ (λ n : El num, (P (int_of_num n)))) (∀ (λ i : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) i) (P i))))) (= (∃ (λ n : El num, (P (int_of_num n)))) (∃ (λ i : El int, (∧ (int_le (int_of_num (NUMERAL _0)) i) (P i))))));
