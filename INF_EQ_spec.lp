require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5205408 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (⇒ (∀ (λ a : El real, (= (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le a x)))) (∀ (λ x : El real, (⇒ ((@IN real) x t) (real_le a x))))))) (= (inf s) (inf t)))))));
