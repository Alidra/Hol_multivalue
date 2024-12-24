require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5133933 : Prf (∀ (λ s : El (fun real bool), (= (sup s) ((@ε real) (λ a : El real, (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x a)))) (∀ (λ b : El real, (⇒ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))) (real_le a b))))))))));
