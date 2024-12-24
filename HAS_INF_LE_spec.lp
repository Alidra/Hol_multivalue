require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5323606 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (∀ (λ l : El real, (∀ (λ m : El real, (⇒ (∧ (has_inf s l) (∧ (has_inf t m) (∀ (λ y : El real, (⇒ ((@IN real) y t) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_le x y))))))))) (real_le l m))))))))));
