require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem297909 [A] : Prf (∀ (λ P : El (fun num (fun A bool)), (∀ (λ R : El (fun num (fun A (fun A bool))), (∀ (λ a : El A, (⇒ (∧ (P (NUMERAL _0) a) (∀ (λ n : El num, (∀ (λ x : El A, (⇒ (P n x) (∃ (λ y : El A, (∧ (P (SUC n) y) (R n x y)))))))))) (∃ (λ f : El (fun num A), (∧ (= (f (NUMERAL _0)) a) (∧ (∀ (λ n : El num, (P n (f n)))) (∀ (λ n : El num, (R n (f n) (f (SUC n))))))))))))))));
