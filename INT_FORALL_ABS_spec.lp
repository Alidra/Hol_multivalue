require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2317738 : Prf (∀ (λ P : El (fun int bool), (= (∀ (λ n : El num, (P (int_of_num n)))) (∀ (λ x : El int, (P (int_abs x)))))));
