require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2296993 : Prf (∀ (λ P : El (fun int bool), (= (∀ (λ x : El int, (P x))) (∧ (∀ (λ n : El num, (P (int_of_num n)))) (∀ (λ n : El num, (P (int_neg (int_of_num n)))))))));
