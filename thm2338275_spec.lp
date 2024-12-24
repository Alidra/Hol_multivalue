require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338275 (P : El (fun int bool)) : Prf (= ((λ P' : El (fun int bool), (= (∀ (λ i : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) i) (P' i)))) (∀ (λ n : El num, (P' (int_of_num n)))))) P) (= (∀ (λ i : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) i) (P i)))) (∀ (λ n : El num, (P (int_of_num n))))));
