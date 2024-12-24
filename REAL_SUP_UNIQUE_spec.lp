require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5158930 : Prf (∀ (λ s : El (fun real bool), (∀ (λ b : El real, (⇒ (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))) (∀ (λ b' : El real, (⇒ (real_lt b' b) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt b' x)))))))) (= (sup s) b))))));
