require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7149041 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A real), (∀ (λ b : El real, (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_lt (f x) (real_div b (real_of_num ((@CARD A) s))))))))) (real_lt ((@sum A) s f) b))))))));
