require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7109270 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ b : El real, (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (real_of_num (NUMERAL _0)) (f x))))) (real_le ((@sum A) s f) b))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (f x) b)))))))))));
