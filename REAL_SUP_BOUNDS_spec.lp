require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5166478 : Prf (∀ (λ s : El (fun real bool), (∀ (λ a : El real, (∀ (λ b : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∀ (λ x : El real, (⇒ ((@IN real) x s) (∧ (real_le a x) (real_le x b)))))) (∧ (real_le a (sup s)) (real_le (sup s) b)))))))));
