require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2339319 (P : El (fun int bool)) : Prf (= (∃ (λ x : El int, (∧ (int_le (int_of_num (NUMERAL _0)) x) (P x)))) (∃ (λ x : El int, (∧ (int_le (int_of_num (NUMERAL _0)) x) (∧ (P x) (∀ (λ y : El int, (⇒ (∧ (int_le (int_of_num (NUMERAL _0)) y) (P y)) (int_le x y)))))))));
