require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066092 [A] : Prf (∧ (∀ (λ a : El A, (∀ (λ f : El (fun num A), (= ((@FCONS A) a f (NUMERAL _0)) a))))) (∀ (λ a : El A, (∀ (λ f : El (fun num A), (∀ (λ n : El num, (= ((@FCONS A) a f (SUC n)) (f n)))))))));
