require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5184172 : Prf (∀ (λ s : El (fun real bool), (∀ (λ a : El real, (∀ (λ b : El real, (∀ (λ y : El real, (⇒ (∧ ((@IN real) y s) (∧ (real_le a y) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))))) (real_le a (sup s)))))))))));
