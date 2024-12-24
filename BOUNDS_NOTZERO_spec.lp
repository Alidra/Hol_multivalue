require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1261658 : Prf (∀ (λ P : El (fun num (fun num num)), (∀ (λ A : El num, (∀ (λ B : El num, (⇒ (∧ (= (P (NUMERAL _0) (NUMERAL _0)) (NUMERAL _0)) (∀ (λ m : El num, (∀ (λ n : El num, (<= (P m n) (+ (* A (+ m n)) B))))))) (∃ (λ B' : El num, (∀ (λ m : El num, (∀ (λ n : El num, (<= (P m n) (* B' (+ m n))))))))))))))));
