require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem245931 : Prf (∀ (λ P : El (fun num bool), (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (∃ (λ a : El num, (P (MOD a n)))) (∃ (λ a : El num, (∧ (< a n) (P a))))))))));
