require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2315380 : Prf (∀ (λ P : El (fun int bool), (= (∀ (λ n : El num, (P (int_of_num n)))) (∀ (λ i : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) i) (P i)))))));
