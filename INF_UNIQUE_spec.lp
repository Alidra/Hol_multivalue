require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5275334 : Prf (∀ (λ s : El (fun real bool), (∀ (λ b : El real, (⇒ (∀ (λ c : El real, (= (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le c x)))) (real_le c b)))) (= (inf s) b))))));
