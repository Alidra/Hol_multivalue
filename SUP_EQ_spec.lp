require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5135108 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (⇒ (∀ (λ b : El real, (= (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))) (∀ (λ x : El real, (⇒ ((@IN real) x t) (real_le x b))))))) (= (sup s) (sup t)))))));
