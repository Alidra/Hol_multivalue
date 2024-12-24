require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7132622 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A real), (∀ (λ b : El real, (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (f x) b))))) (real_le ((@sum A) s f) (real_mul (real_of_num ((@CARD A) s)) b)))))))));
