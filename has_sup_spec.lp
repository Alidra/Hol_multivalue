require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5291214 : Prf (∀ (λ s : El (fun real bool), (∀ (λ b : El real, (= (has_sup s b) (∀ (λ c : El real, (= (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x c)))) (real_le b c)))))))));
