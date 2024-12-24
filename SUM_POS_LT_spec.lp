require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7078795 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (real_of_num (NUMERAL _0)) (f x))))) (∃ (λ x : El A, (∧ ((@IN A) x s) (real_lt (real_of_num (NUMERAL _0)) (f x))))))) (real_lt (real_of_num (NUMERAL _0)) ((@sum A) s f)))))));
