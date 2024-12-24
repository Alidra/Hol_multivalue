require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2749910 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ m : El (fun A int), (⇒ (∧ (∀ (λ x : El A, (int_le (int_of_num (NUMERAL _0)) (m x)))) (∀ (λ x : El A, (⇒ (∀ (λ y : El A, (⇒ (int_lt (m y) (m x)) (P y)))) (P x))))) (∀ (λ x : El A, (P x))))))));
